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

use super::assumptions::{
	AssumptionContext, AssumptionKind, QueryError, QueryResult,
};
use super::bounds::{BoundId, Readiness};
use super::defs::{AssocTypeIdx, DefinitionRegistry, TraitIdx};
use super::obligations::{BoundRequirements, Obligation};
use super::signatures::TypeContext;
use super::types::{Type, TypeEnvIdx, TypeIndex, TypeParam};
use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

impl TypeContext<'_, '_, '_> {
	/// Prove membership from declaration-local assumptions before dispatching
	/// concrete impls. Impl requirements are proved in this same caller context.
	pub(super) fn check_trait(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		trait_index: TraitIdx,
		reference: SourceSpan,
	) -> QueryResult<bool> {
		self.find_trait_impl_query(cx, ty, trait_index, reference)
			.map(|provider| provider.is_some())
	}

	/// Direct facts are the fast path. Otherwise compare the requested type
	/// with subjects that carry this trait in the active scope. Comparison
	/// reduces assumed equalities only, so it cannot depend on impl dispatch.
	pub(super) fn check_assumed_trait(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		required: TraitIdx,
		reference: SourceSpan,
	) -> QueryResult<bool> {
		let mut readiness = Readiness::Ready;
		if matches!(
			self.types.resolve(ty),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			self.prepare_effective_bounds(ty, reference)
				.map_err(|()| QueryError::Failed)?;
			readiness = self.effective_bounds(ty).readiness;
			if self.has_effective_trait(ty, required) {
				return Ok(true);
			}
		}
		// Retain only scalar subjects of relevant memberships. The borrowed
		// cursor must be released before normalization can demand signatures.
		let mut subjects = Vec::new();
		let mut equality_subjects = Vec::new();
		{
			let (reader, types) = self.assumptions();
			let mut facts = reader.scoped_facts(cx, types);
			readiness = readiness.and(facts.readiness);
			while let Some(fact) = facts.next(types) {
				if matches!(
					fact.kind,
					AssumptionKind::Equality(
						super::bounds::ImpliedBindingKind::Equals(_)
					)
				) {
					equality_subjects.push(fact.subject);
				}
				if matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == required)
				{
					if fact.subject == ty {
						return Ok(true);
					}
					if !subjects.contains(&fact.subject) {
						subjects.push(fact.subject);
					}
				}
			}
		}
		// A written equality also gives a finite projection path on which
		// associated declaration bounds may supply evidence (Item: Marker).
		// Read those paths without recursively expanding every declaration.
		for subject in equality_subjects {
			self.prepare_effective_bounds(subject, reference)
				.map_err(|()| QueryError::Failed)?;
			let remaining_depth = self.normalization.remaining_depth();
			let (reader, types) = self.assumptions();
			let mut facts =
				reader.subject_facts(subject, types, remaining_depth);
			readiness = readiness.and(facts.readiness);
			while let Some(fact) = facts.next(types) {
				if matches!(fact.kind, AssumptionKind::Trait { trait_index, .. } if trait_index == required)
				{
					if fact.subject == ty {
						return Ok(true);
					}
					if !subjects.contains(&fact.subject) {
						subjects.push(fact.subject);
					}
				}
			}
		}
		if !subjects.is_empty() {
			let normalized =
				self.normalize_assumed_type_query(cx, ty, reference)?;
			for subject in subjects {
				match self.normalize_assumed_type_query(cx, subject, reference)
				{
					Ok(candidate)
						if candidate == normalized
							&& candidate != TypeIndex::ERROR =>
					{
						return Ok(true);
					}
					Ok(_) => {}
					Err(QueryError::Pending) => {
						readiness = readiness.and(Readiness::Pending)
					}
					Err(QueryError::Failed) => return Err(QueryError::Failed),
				}
			}
		}
		match readiness {
			Readiness::Ready => Ok(false),
			Readiness::Pending => Err(QueryError::Pending),
			Readiness::Overflowed => {
				Err(self.normalization_overflow(reference))
			}
		}
	}

	fn requirement_facts(
		&self,
		requirements: BoundRequirements,
	) -> QueryResult<&[super::bounds::ImpliedTraitBound]> {
		let facts = match requirements {
			BoundRequirements::Parameter { env, index } => {
				&self.param_bounds[usize::from(env)][index].facts
			}
			BoundRequirements::AssociatedType(index) => {
				let Some(signature) = &self.assoc_types[usize::from(index)]
				else {
					return Err(QueryError::Pending);
				};
				&signature.facts
			}
		};
		if !facts.is_ready() {
			return Err(QueryError::Pending);
		}
		Ok(facts.current())
	}

	/// Gather violations before emitting them: another requirement can still
	/// be pending, and a retry must not duplicate a diagnostic.
	fn check_requirements(
		&mut self,
		cx: AssumptionContext,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> QueryResult<()> {
		let count = self.requirement_facts(requirements)?.len();
		let mut violations = Vec::new();
		for index in 0..count {
			let bound = &self.requirement_facts(requirements)?[index];
			let (required, source) = (bound.trait_index, bound.source);
			if !self.check_trait(cx, argument.inner, required, reference)? {
				violations.push((required, source));
			}
		}
		let valid = violations.is_empty();
		for (required, source) in violations {
			let diagnostic = self.report_trait_bound_violation(
				reference.file_id,
				argument,
				required,
				source,
				owner,
			);
			self.diagnostics.push(diagnostic);
		}
		if valid {
			Ok(())
		} else {
			Err(QueryError::Failed)
		}
	}

	pub(super) fn check_obligation(
		&mut self,
		obligation: &Obligation,
	) -> QueryResult<TypeIndex> {
		match *obligation {
			Obligation::CheckBounds {
				context,
				requirements,
				argument,
				reference,
				owner,
			} => self
				.check_requirements(
					context,
					requirements,
					argument,
					reference,
					owner,
				)
				.map(|()| argument.inner),
			Obligation::Normalize {
				context,
				subject,
				reference,
			} => {
				let normalized =
					self.normalize_type_query(context, subject, reference)?;
				if normalized == TypeIndex::ERROR {
					Err(QueryError::Failed)
				} else {
					Ok(normalized)
				}
			}
			Obligation::CheckTraitMembership {
				context,
				subject,
				required,
				reference,
			} => {
				if self
					.find_trait_impl_query(
						context, subject, required, reference,
					)?
					.is_some()
				{
					return Ok(subject);
				}
				let diagnostic = self.report_type_does_not_implement_trait(
					reference.file_id,
					reference.span,
					subject,
					required,
				);
				self.diagnostics.push(diagnostic);
				Err(QueryError::Failed)
			}
		}
	}

	fn validate_or_defer(
		&mut self,
		cx: AssumptionContext,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> TypeIndex {
		match self.check_requirements(
			cx,
			requirements,
			argument,
			reference,
			owner,
		) {
			Ok(()) => argument.inner,
			Err(QueryError::Failed) => TypeIndex::ERROR,
			Err(QueryError::Pending) => {
				self.register_obligation(Obligation::CheckBounds {
					context: cx,
					requirements,
					argument,
					reference,
					owner,
				});
				argument.inner
			}
		}
	}

	/// Checks a provided associated-type value against the trait's own
	/// declared bound for that member (forcing it first). Synthetic memory
	/// sizes still use this existing check. Equality fact collection and
	/// written impl providers leave conformance checking to a later phase.
	/// `declared_assoc_type` must be the trait's own declaration (`TraitAssocType`'s own
	/// `AssocTypeIdx`), never an impl's provided-value slot — same
	/// requirement `ensure_assoc_type_bounds` already has, which this
	/// forces first.
	///
	/// Completed violations recover with `ERROR`. Unfinished requirements
	/// retain the symbolic value and defer checking to its owning query.
	/// An already diagnosed declaration cycle does not add another diagnostic.
	pub(super) fn check_assoc_type_value(
		&mut self,
		cx: AssumptionContext,
		declared_assoc_type: AssocTypeIdx,
		value: Spanned<TypeIndex>,
		file_id: FileId,
		owner: TypeEnvOwner,
	) -> TypeIndex {
		let reference = SourceSpan::new(file_id, value.span);
		if self
			.ensure_assoc_type_bounds(declared_assoc_type, reference)
			.is_err()
		{
			return value.inner;
		}
		self.validate_or_defer(
			cx,
			BoundRequirements::AssociatedType(declared_assoc_type),
			value,
			reference,
			owner,
		)
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
		cx: AssumptionContext,
		file_id: FileId,
		reference_span: TextSpan,
		params_env: TypeEnvIdx,
		args: &[Spanned<TypeIndex>],
		owner: TypeEnvOwner,
	) -> Box<[TypeIndex]> {
		let expected = self.param_bounds[usize::from(params_env)].len();
		if args.len() != expected {
			self.diagnostics.push(report_type_arg_count_mismatch(
				self.strings,
				self.defs,
				file_id,
				reference_span,
				self.type_envs.frame(params_env),
				args,
				owner,
			));
			return vec![TypeIndex::ERROR; expected].into_boxed_slice();
		}

		let mut result = Vec::with_capacity(expected);
		for (index, argument) in args.iter().copied().enumerate() {
			result.push(self.validate_or_defer(
				cx,
				BoundRequirements::Parameter {
					env: params_env,
					index,
				},
				argument,
				SourceSpan::new(file_id, argument.span),
				owner,
			));
		}
		result.into_boxed_slice()
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
			.resolve(self.defs.traits[usize::from(trait_index)].name.inner)
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
							.resolve(owner.name(self.defs).unwrap().inner)
							.unwrap()
					),
				),
			)
	}
}

/// `params` is the target's own frame, straight from `TypeEnvArena` — reads
/// each `EnvParam`'s own (already `pub(super)`) `name` field directly rather
/// than going through a single-index accessor per name/span, since nothing
/// here needs `param`'s own resolved `ty` or `accesses`.
pub(super) fn report_type_arg_count_mismatch(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	reference_span: TextSpan,
	params: &[TypeParam],
	args: &[Spanned<TypeIndex>],
	owner: TypeEnvOwner,
) -> Diagnostic<FileId> {
	let owner_file_id = owner.file_id(defs);
	let owner_name = owner.name(defs).unwrap();
	let expected = params.len();
	let found = args.len();
	let plural = |n: usize| if n == 1 { "" } else { "s" };

	let mut labels = vec![
		SourceSpan::new(file_id, reference_span)
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

	let owner_str = strings.resolve(owner_name.inner).unwrap();
	labels.push(
		SourceSpan::new(owner_file_id, owner_name.span)
			.secondary_label()
			.with_message(format!(
				"{} defined here, with {expected} generic parameter{}",
				owner.noun(),
				plural(expected)
			)),
	);
	for param in params {
		labels.push(
			SourceSpan::new(owner_file_id, param.name.span).secondary_label(),
		);
	}

	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentCountMismatch.code())
		.with_message(format!(
			"{} `{owner_str}` takes {expected} generic argument{} but {found} generic argument{} {} supplied",
			owner.noun(),
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
	use crate::tir::defs::{BindingNamespace, DefKind, DefinitionRegistry};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::paths::PathResolver;
	use crate::tir::signatures::QueryInfo;
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
		let (defs, ast_nodes) = DefinitionRegistry::build(
			&graph.packages,
			&graph.files,
			&mut graph.strings,
			&mut diagnostics,
			graph.stdlib_package,
			graph.root_package,
		);
		let impl_dispatch = ImplDispatch::build(
			&mut diagnostics,
			&graph.strings,
			&defs,
			&ast_nodes,
		);
		let mut builder = TypeContext::new(
			&mut diagnostics,
			&graph.strings,
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
		tier: BindingNamespace,
		path: &str,
	) -> DefKind {
		let root = graph.root_package.root_namespace();
		let file_id = builder.defs.namespaces[usize::from(root)].file_id;

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
		let target = PathResolver::new(builder.defs).resolve_path(
			&mut diagnostics,
			&graph.strings,
			file_id,
			root,
			&segments,
			tier,
		);
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
			resolve(builder, graph, BindingNamespace::Type, path)
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
			resolve(builder, graph, BindingNamespace::Type, path)
		else {
			panic!("expected `{path}` to be a typeset");
		};
		builder.defs.typesets[usize::from(typeset_index)].trait_index
	}

	/// `path`'s own `TypeIndex` — a non-generic struct only (a generic
	/// struct's instantiated `TypeIndex` needs type-argument resolution,
	/// which isn't implemented yet — see `impls.rs::resolve_impl_target`).
	fn struct_type(
		builder: &mut TypeContext,
		graph: &vfs::CompilationUnit,
		path: &str,
	) -> TypeIndex {
		let DefKind::Struct(struct_index) =
			resolve(builder, graph, BindingNamespace::Type, path)
		else {
			panic!("expected `{path}` to be a struct");
		};
		builder.types.intern(Type::Struct {
			struct_index,
			type_args: Box::new([]),
		})
	}

	/// The `TypeIndex` of `function_path`'s `param_index`-th own declared
	/// generic parameter — e.g. the `T` in `fn target<T: Bound>(x: T)`.
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
			resolve(builder, graph, BindingNamespace::Value, function_path)
		else {
			panic!("expected `{function_path}` to be a function");
		};
		let env = builder.functions[usize::from(function_index)].type_params;
		builder.types.intern(Type::TypeParam { env, param_index })
	}

	fn dummy_reference(
		builder: &TypeContext,
		graph: &vfs::CompilationUnit,
	) -> SourceSpan {
		let root = graph.root_package.root_namespace();
		let file_id = builder.defs.namespaces[usize::from(root)].file_id;
		SourceSpan::new(file_id, TextSpan::new(0, 0))
	}

	#[test]
	fn error_and_infer_are_recovery_not_proofs() {
		with_resolved(
			indoc! {"
			trait Foo {}
		"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let foo = trait_index(builder, graph, "Foo");
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						TypeIndex::ERROR,
						foo,
						reference
					) == Err(QueryError::Failed))
				);
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						TypeIndex::INFER,
						foo,
						reference
					) == Err(QueryError::Failed))
				);
			},
		);
	}

	#[test]
	fn a_struct_with_a_matching_impl_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				trait Foo {}
				struct S {}
				impl Foo for S {}
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let foo = trait_index(builder, graph, "Foo");
				let s = struct_type(builder, graph, "S");
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						s,
						foo,
						reference
					) == Ok(true))
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
				struct S {}
				impl Foo for S {}
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let bar = trait_index(builder, graph, "Bar");
				let s = struct_type(builder, graph, "S");
				assert!(
					!(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						s,
						bar,
						reference
					) == Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_struct_listed_in_a_typeset_satisfies_its_backing_trait() {
		with_resolved(
			indoc! {"
				struct S {}
				typeset Nums { S }
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let nums = typeset_trait_index(builder, graph, "Nums");
				let s = struct_type(builder, graph, "S");
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						s,
						nums,
						reference
					) == Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_with_a_matching_bound_satisfies_the_trait() {
		with_resolved(
			indoc! {"
				trait Bound {}
				fn target<T: Bound>(x: T) {}
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let bound = trait_index(builder, graph, "Bound");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						t,
						bound,
						reference
					) == Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_without_the_bound_does_not_satisfy_the_trait() {
		with_resolved(
			indoc! {"
				trait Bound {}
				trait Other {}
				fn target<T: Bound>(x: T) {}
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let other = trait_index(builder, graph, "Other");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					!(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						t,
						other,
						reference
					) == Ok(true))
				);
			},
		);
	}

	#[test]
	fn a_generic_param_satisfies_a_bounds_supertrait_transitively() {
		with_resolved(
			indoc! {"
				trait Super {}
				trait Sub: Super {}
				fn target<T: Sub>(x: T) {}
			"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let super_trait = trait_index(builder, graph, "Super");
				let t = generic_param_type(builder, graph, "target", 0);
				assert!(
					(builder.check_trait(
						AssumptionContext::new(TypeEnvIdx::ROOT),
						t,
						super_trait,
						reference
					) == Ok(true))
				);
			},
		);
	}
}
