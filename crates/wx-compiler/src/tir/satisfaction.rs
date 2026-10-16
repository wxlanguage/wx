//! Trait-bound satisfaction: does a resolved type actually satisfy a
//! required trait? The question everything else that checks a bound —
//! impl-target validation, call-site type-argument checking, `where`-clause
//! verification — will eventually go through, once any of those exist.
//!
//! Concrete membership uses dispatch candidate discovery followed by full
//! impl-target matching. Abstract membership reads the same effective facts
//! as normalization and member lookup. This module does not prove associated
//! equality requirements or validate impl conformance.

use codespan_reporting::diagnostic::Diagnostic;

use super::bounds::BoundId;
use string_interner::symbol::SymbolU32;

use super::defs::{BindingKey, DefKind, DefinitionRegistry, TraitIdx};
use super::impls::ImplTarget;
use super::members::{MemberLookup, report_no_such_type_member};
use super::obligations::{BoundRequirements, Obligation, ObligationChecker};
use super::signatures::TypeContext;
use super::solver::SolverError;
use super::types::{Type, TypeEnvIdx, TypeIndex, TypeParam};
use crate::ast::{self, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::tir::bounds::{BoundFacts, ImpliedTraitBound};
use crate::tir::solver::SolverView;
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

impl TypeContext<'_, '_, '_> {
	/// Records the check of `argument` against `requirements` for the check
	/// pass. Construction never decides a bound: the argument is kept as
	/// written, and a failure is diagnosed later without rewriting it.
	pub(super) fn record_bounds_check(
		&mut self,
		assumption_context: TypeEnvIdx,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> TypeIndex {
		self.register_obligation(Obligation::CheckBounds {
			assumption_context,
			requirements,
			argument,
			reference,
			owner,
		});
		argument.inner
	}

	/// Resolves a written type-argument list against `params_env`'s own
	/// declared parameters — the count comes from `params_env` itself
	/// (`self.param_bounds[params_env].len()`), never a separately-passed
	/// number, so it can't drift from what the frame actually declares.
	/// Always returns exactly that many slots.
	///
	/// A wrong count poisons every slot to `ERROR` — there's no sensible
	/// pairing to salvage — but keeps `owner_name`'s own identity meaningful
	/// to whatever reads the result next (a caller still sees "a `Wrapper`",
	/// not a second, unrelated "not a struct" error stacked on this one). A
	/// correct count checks each argument, in its own right, against every
	/// bound its corresponding parameter declares — reported per failing
	/// bound, same granularity as `T: A + B` needing two diagnostics if an
	/// argument satisfies neither — and only that one slot, not the whole
	/// list, is poisoned when any of them fails. Pending requirements retain
	/// the argument and enqueue a check against the eventual parameter table.
	pub(super) fn resolve_type_args(
		&mut self,
		assumption_context: TypeEnvIdx,
		file_id: FileId,
		segment: &ast::PathSegment,
		params_env: TypeEnvIdx,
		args: &[TypeIndex],
		owner: TypeEnvOwner,
	) -> Box<[TypeIndex]> {
		let expected = self.param_bounds[usize::from(params_env)].len();
		if args.len() != expected {
			self.diagnostics.push(report_type_arg_count_mismatch(
				self.strings,
				self.defs,
				file_id,
				segment,
				TypeArgsTarget::Item {
					owner,
					params: self.type_envs.params(params_env),
				},
			));
			return vec![TypeIndex::ERROR; expected].into_boxed_slice();
		}

		let mut result = Vec::with_capacity(expected);
		for (index, (&argument, written)) in
			args.iter().zip(&segment.type_args).enumerate()
		{
			result.push(self.record_bounds_check(
				assumption_context,
				BoundRequirements::Parameter {
					env: params_env,
					index,
				},
				Spanned {
					inner: argument,
					span: written.span,
				},
				SourceSpan::new(file_id, written.span),
				owner,
			));
		}
		result.into_boxed_slice()
	}
}

impl<'a> SolverView<'a> {
	/// The facts live in the shared tables, not in the view, so they outlive
	/// this borrow of it: a caller can read them while it lends the view on.
	fn requirement_facts(
		&self,
		requirements: BoundRequirements,
	) -> Result<&'a [ImpliedTraitBound], ()> {
		// Copied out, so indexing yields `'a` rather than this `&self`.
		let (param_bounds, assoc_types) = (self.param_bounds, self.assoc_types);
		let facts = match requirements {
			BoundRequirements::Parameter { env, index } => {
				&param_bounds[usize::from(env)][index].facts
			}
			BoundRequirements::AssociatedType(index) => {
				let Some(signature) = &assoc_types[usize::from(index)] else {
					return Err(());
				};
				&signature.facts
			}
		};
		match facts {
			BoundFacts::Ready(facts) => Ok(facts),
			BoundFacts::Provisional(_) => Err(()),
		}
	}
}

/// The checks bound satisfaction owns, run by the declaration check.
impl ObligationChecker<'_> {
	/// Gather violations before emitting them: another requirement can still
	/// be pending, and a retry must not duplicate a diagnostic.
	pub(super) fn check_requirements(
		&mut self,
		assumption_context: TypeEnvIdx,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> Result<(), SolverError> {
		let mut result = Ok(());
		for bound in self
			.view
			.requirement_facts(requirements)
			.map_err(|_| SolverError::Pending)?
		{
			if self
				.solver
				.find_trait_impl_query(
					&mut self.view,
					assumption_context,
					argument.inner,
					bound.trait_index,
				)?
				.is_none()
			{
				let diagnostic = self.report_trait_bound_violation(
					reference.file_id,
					argument,
					bound.trait_index,
					bound.source,
					owner,
				);
				self.diagnostics.push(diagnostic);
				result = Err(SolverError::Poisoned);
			}
		}
		result
	}

	/// `projection::name` could not be selected from the projection's declared
	/// bounds. Resolve what the projection's value is and which traits could
	/// supply `name` on it, as rustc does to build its suggestion. Selecting
	/// through an impl unqualified is ambiguous by design, so a trait that
	/// *would* work is still an error, but one that says how to write it.
	/// Always fails: the lowered type was `ERROR`.
	pub(super) fn check_projection_member(
		&mut self,
		assumption_context: TypeEnvIdx,
		projection: TypeIndex,
		name: SymbolU32,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		let key = BindingKey::ty(name);
		let ident = Spanned {
			inner: name,
			span: reference.span,
		};
		let declared_anywhere = (0..self.view.defs.traits.len()).any(|index| {
			self.view
				.defs
				.declared_trait_member(TraitIdx::new(index as u32), key)
				.is_some()
		});
		let normalized = match self.solver.normalize_head_query(
			&mut self.view,
			assumption_context,
			projection,
		) {
			Ok(normalized) => normalized,
			// The projection has no value (an impl omits it, or its own
			// requirement failed); that is reported where it belongs. Only a
			// name no trait declares is certainly wrong.
			Err(SolverError::Poisoned) => {
				if !declared_anywhere {
					self.diagnostics.push(report_no_such_type_member(
						reference.file_id,
						self.strings,
						ident,
					));
				}
				return Err(SolverError::Poisoned);
			}
			Err(error) => return Err(error),
		};
		// Each source names a trait at most once: the dispatch index holds one
		// impl per trait per type constructor, and `declared_bound_member` skips
		// a trait it has already collected.
		let mut traits: Vec<TraitIdx> = Vec::new();
		match ImplTarget::from_type(self.view.types.resolve(normalized)) {
			Some(target) => {
				for &(trait_index, _) in
					self.view.impl_dispatch.trait_candidates(target)
				{
					if self
						.view
						.defs
						.declared_trait_member(trait_index, key)
						.is_some()
					{
						traits.push(trait_index);
					}
				}
			}
			// Every signature exists, so the bounds are ready to read.
			None if matches!(
				self.view.types.resolve(normalized),
				Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
			) =>
			{
				let bounds = self.view.effective_bounds(
					normalized,
					self.solver.state.recursion_budget,
				);
				match TypeContext::select_declared_member(
					self.view.defs,
					bounds,
					key,
				) {
					MemberLookup::Found(member) => {
						traits.extend(
							member
								.assoc_type_declaration()
								.map(|d| d.trait_index),
						);
					}
					MemberLookup::Ambiguous(members) => {
						traits.extend(members.iter().filter_map(|member| {
							member
								.assoc_type_declaration()
								.map(|d| d.trait_index)
						}));
					}
					_ => {}
				}
			}
			None => {}
		}
		if traits.is_empty() {
			self.diagnostics.push(report_no_such_type_member(
				reference.file_id,
				self.strings,
				ident,
			));
			return Err(SolverError::Poisoned);
		}
		let name_str = self.strings.resolve(name).unwrap().to_string();
		let receiver = self.type_formatter().display_type(projection);
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TypeMemberNeedsQualification.code())
			.with_message(format!("ambiguous associated type `{name_str}`"))
			.with_label(reference.primary_label().with_message(format!(
				"`{receiver}` is known only through an impl, so the trait must be named"
			)));
		for trait_index in traits {
			let trait_name = self
				.strings
				.resolve(
					self.view.defs.traits[usize::from(trait_index)].name.inner,
				)
				.unwrap();
			diagnostic = diagnostic.with_note(format!(
				"qualify the trait: `<{receiver} as {trait_name}>::{name_str}`"
			));
		}
		self.diagnostics.push(diagnostic);
		Err(SolverError::Poisoned)
	}

	fn report_trait_bound_violation(
		&self,
		file_id: FileId,
		argument: Spanned<TypeIndex>,
		trait_index: TraitIdx,
		bound_id: BoundId,
		owner: TypeEnvOwner,
	) -> Diagnostic<FileId> {
		let arg_name = self.type_formatter().display_type(argument.inner);
		let trait_name = self
			.strings
			.resolve(self.view.defs.traits[usize::from(trait_index)].name.inner)
			.unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the trait bound `{arg_name}: {trait_name}` is not satisfied"
			))
			.with_label(
				SourceSpan::new(file_id, argument.span)
					.primary_label()
					.with_message(format!(
						"the trait `{trait_name}` is not implemented for `{arg_name}`"
					)),
			)
			.with_label(
				self.bounds.span(bound_id).secondary_label().with_message(
					format!(
						"required by a bound in `{}`",
						self.strings
							.resolve(owner.name(self.view.defs).unwrap().inner)
							.unwrap()
					),
				),
			)
	}
}

/// What a path segment written with generic arguments names.
pub(super) enum TypeArgsTarget<'a> {
	/// A declaration and its own generic parameters, possibly none.
	Item {
		owner: TypeEnvOwner,
		params: &'a [TypeParam],
	},
	/// A generic parameter or `Self`, which has no parameter list.
	TypeParam,
	/// A namespace the path passes through, which has no parameter list.
	Namespace(DefKind),
}

pub(super) fn report_type_arg_count_mismatch(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	segment: &ast::PathSegment,
	target: TypeArgsTarget<'_>,
) -> Diagnostic<FileId> {
	let (noun, name, declaration) = match target {
		TypeArgsTarget::Item { owner, params } => {
			let name = owner.name(defs).unwrap();
			let declared_at = SourceSpan::new(owner.file_id(defs), name.span);
			(owner.noun(), name.inner, Some((declared_at, params)))
		}
		TypeArgsTarget::TypeParam
			if segment.ident.inner == Keyword::SelfPascal.symbol() =>
		{
			("self type", segment.ident.inner, None)
		}
		TypeArgsTarget::TypeParam => {
			("type parameter", segment.ident.inner, None)
		}
		TypeArgsTarget::Namespace(kind) => {
			(kind.noun(), segment.ident.inner, None)
		}
	};
	let args = &segment.type_args;
	let params = declaration.map_or(&[][..], |(_, params)| params);
	let expected = params.len();
	let found = args.len();
	let plural = |n: usize| if n == 1 { "" } else { "s" };

	let mut labels = vec![
		SourceSpan::new(file_id, segment.ident.span)
			.primary_label()
			.with_message(format!(
				"expected {expected} generic argument{}",
				plural(expected)
			)),
	];
	for (index, arg) in args.iter().enumerate() {
		let label = SourceSpan::new(file_id, arg.span).secondary_label();
		labels.push(if index + 1 == args.len() {
			if expected == 0 {
				label.with_message("remove the unnecessary generics")
			} else {
				label.with_message(format!(
					"supplied {found} generic argument{}",
					plural(found)
				))
			}
		} else {
			label
		});
	}

	if let Some((declared_at, params)) = declaration {
		labels.push(declared_at.secondary_label().with_message(format!(
			"{noun} defined here, with {expected} generic parameter{}",
			plural(expected)
		)));
		for param in params {
			labels.push(
				SourceSpan::new(declared_at.file_id, param.name.span)
					.secondary_label(),
			);
		}
	}

	let name = strings.resolve(name).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentCountMismatch.code())
		.with_message(format!(
			"{noun} `{name}` takes {expected} generic argument{} but {found} generic argument{} {} supplied",
			plural(expected),
			plural(found),
			if found == 1 { "was" } else { "were" },
		))
		.with_labels(labels)
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned};
	use crate::diagnostics::TextSpan;
	use crate::tir::defs::{DefKind, DefinitionRegistry, Scope, Tier};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::types::Type;
	use crate::vfs;

	/// Parses `source` (playing the stdlib's own role, same reasoning as
	/// `signatures::tests::source_graph`), sweeps every registered item's
	/// signature, then hands the live `TypeContext` to `f`. Nothing borrowed
	/// here (`graph`, `defs`, `ast_nodes`, `diagnostics`) may escape this
	/// call; only `f`'s own, owned return value does.
	fn with_resolved<R>(
		source: &str,
		f: impl FnOnce(&mut TypeContext, &vfs::CompilationUnit) -> R,
	) -> R {
		let mut vfs_builder = vfs::CompilationUnitBuilder::new();
		let root_id = vfs_builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(HashMap::from([(
					"main.wx".to_string(),
					source.to_string(),
				)])),
			)
			.unwrap();
		vfs_builder.set_stdlib(root_id);
		let mut graph = vfs_builder.build(root_id);

		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let (defs, ast_nodes) = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			&mut resolutions,
			graph.stdlib_package,
			graph.root_package,
		);
		let impl_dispatch = ImplDispatch::build(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			&defs,
			&ast_nodes,
		);
		let mut builder = TypeContext::new(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			&graph.files,
			&defs,
			&ast_nodes,
			&impl_dispatch,
		);
		builder.sweep();
		assert!(builder.diagnostics.is_empty(), "{:?}", builder.diagnostics);

		f(&mut builder, &graph)
	}

	/// Resolves `path` (`::`-separated) as a `tier`-tier path from the root
	/// namespace — same mechanism a written bound or type actually uses,
	/// mirroring `signatures::tests::TestCase::resolve`.
	fn resolve(
		builder: &TypeContext,
		graph: &vfs::CompilationUnit,
		tier: Tier,
		path: &str,
	) -> DefKind {
		let root = Scope::Package(graph.root_package);
		let file_id = builder.defs.namespaces.file_id(root.into());

		let segments: Box<[ast::PathSegment]> = path
			.split("::")
			.map(|segment| ast::PathSegment {
				ident: Spanned {
					inner: graph
						.strings
						.get(segment)
						.expect("already interned from source"),
					span: TextSpan::new(0, 0),
				},
				type_args: Box::new([]),
			})
			.collect();
		let mut diagnostics = Vec::new();
		let mut resolutions = NameResolutions::default();
		let target = PathResolver::new(
			&mut diagnostics,
			&mut resolutions,
			&graph.strings,
			builder.defs,
		)
		.resolve_path(file_id, root, &segments, tier);
		target
			.def_key()
			.unwrap_or_else(|| {
				panic!("expected `{path}` to resolve: {diagnostics:?}")
			})
			.symbol_kind(builder.defs)
	}

	fn trait_index(
		builder: &TypeContext,
		graph: &vfs::CompilationUnit,
		path: &str,
	) -> TraitIdx {
		let DefKind::Trait(trait_index) =
			resolve(builder, graph, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a trait");
		};
		trait_index
	}

	/// The `TraitIndex` of `path`'s compiler-generated backing trait — what
	/// a `T: <path>` bound naming this typeset actually resolves to. See
	/// `TypeSetSignature`'s own doc comment.
	fn typeset_trait_index(
		builder: &TypeContext,
		graph: &vfs::CompilationUnit,
		path: &str,
	) -> TraitIdx {
		let DefKind::TypeSet(typeset_index) =
			resolve(builder, graph, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a typeset");
		};
		builder.defs.typesets[usize::from(typeset_index)].trait_index
	}

	/// `path`'s own `TypeIndex` — a non-generic struct only(a generic
	/// struct's instantiated `TypeIndex` needs type-argument resolution,
	/// which isn't implemented yet — see `impls.rs::resolve_impl_target`).
	fn struct_type(
		builder: &mut TypeContext,
		graph: &vfs::CompilationUnit,
		path: &str,
	) -> TypeIndex {
		let DefKind::Struct(struct_index) =
			resolve(builder, graph, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a struct");
		};
		builder.types.intern_struct(struct_index, &[])
	}

	/// The `TypeIndex` of `function_path`'s `param_index`-th own declared
	/// generic parameter — e.g. the `T` in `func target<T: Bound>(x: T)`.
	/// Declaring the type under test as a generic function's own type
	/// parameter, rather than reading a resolved parameter type back out of
	/// `FunctionSignature` (private to `signatures.rs` — nothing outside it
	/// needs a function's own resolved types yet), is what lets this same
	/// harness reach a `TypeParam` receiver without a wider accessor.
	fn generic_param_type(
		builder: &mut TypeContext,
		graph: &vfs::CompilationUnit,
		function_path: &str,
		param_index: u32,
	) -> TypeIndex {
		let DefKind::Function(function_index) =
			resolve(builder, graph, Tier::Value, function_path)
		else {
			panic!("expected `{function_path}` to be a function");
		};
		let env = builder.functions[usize::from(function_index)].type_params;
		builder.types.intern(Type::TypeParam { env, param_index })
	}

	#[test]
	fn error_and_infer_are_recovery_not_proofs() {
		with_resolved(
			indoc! {"
			trait Foo {}
		"},
			|builder, graph| {
				let foo = trait_index(builder, graph, "Foo");
				assert!(
					(builder
						.find_trait_impl_query(
							TypeEnvIdx::ROOT,
							TypeIndex::ERROR,
							foo
						)
						.map(|found| found.is_some())
						== Err(SolverError::Poisoned))
				);
				assert!(
					(builder
						.find_trait_impl_query(
							TypeEnvIdx::ROOT,
							TypeIndex::INFER,
							foo
						)
						.map(|found| found.is_some())
						== Err(SolverError::Poisoned))
				);
			},
		);
	}

	#[test]
	fn a_struct_with_a_matching_impl_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				trait Foo {}
				struct S();
				impl Foo for S {}
			"},
			|builder, graph| {
				let foo = trait_index(builder, graph, "Foo");
				let s = struct_type(builder, graph, "S");
				assert!(
					(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, s, foo)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_struct_with_no_impl_does_not_satisfy_the_trait() {
		with_resolved(
			indoc! {"
				trait Foo {}
				trait Bar {}
				struct S();
				impl Foo for S {}
			"},
			|builder, graph| {
				let bar = trait_index(builder, graph, "Bar");
				let s = struct_type(builder, graph, "S");
				assert!(
					!(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, s, bar)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_struct_listed_in_a_typeset_satisfies_its_backing_trait() {
		with_resolved(
			indoc! {"
				struct S();
				typeset Nums { S }
			"},
			|builder, graph| {
				let nums = typeset_trait_index(builder, graph, "Nums");
				let s = struct_type(builder, graph, "S");
				assert!(
					(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, s, nums)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_with_a_matching_bound_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Bound {}
				func target<T: Bound>(x: T) {}
			"},
			|builder, graph| {
				let bound = trait_index(builder, graph, "Bound");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, t, bound)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_without_the_bound_does_not_satisfy_the_trait() {
		with_resolved(
			indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Bound {}
				trait Other {}
				func target<T: Bound>(x: T) {}
			"},
			|builder, graph| {
				let other = trait_index(builder, graph, "Other");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					!(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, t, other)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_satisfies_a_bounds_supertrait_transitively() {
		with_resolved(
			indoc! {"
				pub trait Call { type Args; type Result; } pub trait Function: Call {}
				trait Super {}
				trait Sub: Super {}
				func target<T: Sub>(x: T) {}
			"},
			|builder, graph| {
				let super_trait = trait_index(builder, graph, "Super");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					(builder
						.find_trait_impl_query(TypeEnvIdx::ROOT, t, super_trait)
						.map(|found| found.is_some())
						== Ok(true))
				);
			},
		);
	}
}
