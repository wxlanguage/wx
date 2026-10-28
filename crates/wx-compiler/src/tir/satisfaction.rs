//! Trait-bound satisfaction: does a resolved type actually satisfy a
//! required trait? The question everything else that checks a bound —
//! impl-target validation, call-site type-argument checking, `where`-clause
//! verification — will eventually go through, once any of those exist.
//!
//! Concrete membership uses dispatch candidate discovery followed by full
//! impl-target matching. Abstract membership reads the same clauses as
//! normalization and member lookup. A bound's bindings are proven too: an
//! equality by comparing the normalized projection with the written value, a
//! nested bound on the projection. That proof is `Solver::satisfies_clauses`,
//! shared with impl selection; this module reports its failures. Impl
//! conformance (`conformance.rs`) proves an impl's associated values and its
//! target's supertraits through the same check.

use codespan_reporting::diagnostic::Diagnostic;

use super::bounds::BoundId;
use string_interner::symbol::SymbolU32;

use super::defs::{BindingKey, DefKind, DefinitionRegistry, TraitIdx};
use super::impls::ImplTarget;
use super::members::{MemberLookup, report_no_such_type_member};
use super::obligations::{BoundRequirements, TypeObligation};
use super::signatures::{LexicalScope, TypeContext};
use super::solver::{
	NormalizationDepth, RewriteFlags, SolverError, UnsatisfiedClause,
};
use super::types::{Type, TypeEnvIdx, TypeIndex};
use crate::ast::{self, Keyword, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::bounds::{BindingRef, BindingRequirement};
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

impl TypeContext<'_, '_, '_> {
	/// Records the check of `argument` against `requirements` in
	/// `obligations`, for whoever lowers it to check. Construction never decides a bound: the argument is kept as
	/// written, and a failure is diagnosed later without rewriting it.
	pub(super) fn record_bounds_check(
		&mut self,
		obligations: &mut Vec<TypeObligation>,
		assumption_context: TypeEnvIdx,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> TypeIndex {
		obligations.push(TypeObligation::CheckBounds {
			assumption_context,
			requirements,
			argument,
			reference,
			owner,
		});
		argument.inner
	}

	/// Resolves a written type-argument list against `params_env`, `owner`'s
	/// own frame (`ROOT` when it declares no parameters). Always returns as
	/// many arguments as the frame declares. A wrong count is reported and
	/// makes every one `ERROR`: there is no sensible pairing to salvage, and
	/// the caller still sees a `Wrapper`, not a second "not a struct" error.
	/// Otherwise the arguments are kept as written, and each one's bounds are
	/// recorded at the argument, so `T: A + B` is two reports when an
	/// argument satisfies neither. `parent_args` are the arguments of the
	/// frames around `params_env`, outer first, which a bound may name.
	pub(super) fn resolve_type_args(
		&mut self,
		obligations: &mut Vec<TypeObligation>,
		scope: LexicalScope,
		segment: &ast::PathSegment,
		params_env: TypeEnvIdx,
		parent_args: &[TypeIndex],
		args: &[TypeIndex],
		owner: TypeEnvOwner,
	) -> Box<[TypeIndex]> {
		if !self.check_type_arg_count(scope, segment, params_env, owner) {
			let expected = self.param_bounds[usize::from(params_env)].len();
			return vec![TypeIndex::ERROR; expected].into_boxed_slice();
		}
		if args.is_empty() {
			return Box::new([]);
		}
		debug_assert_eq!(
			parent_args.len(),
			self.type_envs.parent_count(params_env),
			"a bound is substituted over the frame's whole chain"
		);
		let arguments = self.types.push_list(parent_args.iter().chain(args));
		for (index, (&argument, written)) in
			args.iter().zip(&segment.type_args).enumerate()
		{
			self.record_bounds_check(
				obligations,
				scope.env,
				BoundRequirements::Parameter {
					env: params_env,
					index,
					arguments,
				},
				Spanned {
					inner: argument,
					span: written.span(),
				},
				SourceSpan::new(scope.file_id, written.span()),
				owner,
			);
		}
		args.into()
	}

	/// Whether `segment` writes as many type arguments as `params_env`
	/// declares; reports the mismatch when it does not.
	pub(super) fn check_type_arg_count(
		&mut self,
		scope: LexicalScope,
		segment: &ast::PathSegment,
		params_env: TypeEnvIdx,
		owner: TypeEnvOwner,
	) -> bool {
		let expected = self.param_bounds[usize::from(params_env)].len();
		if segment.type_args.len() == expected {
			return true;
		}
		self.diagnostics.push(report_type_arg_count_mismatch(
			self.strings,
			self.defs,
			scope.file_id,
			segment,
			owner,
			self.type_envs.param_names(params_env),
		));
		false
	}
}

/// The checks bound satisfaction owns, run by the declaration check.
impl TypeContext<'_, '_, '_> {
	/// Gather violations before emitting them: another requirement can still
	/// be pending, and a retry must not duplicate a diagnostic.
	pub(super) fn check_bound_requirements(
		&mut self,
		assumption_context: TypeEnvIdx,
		requirements: BoundRequirements,
		argument: Spanned<TypeIndex>,
		reference: SourceSpan,
		owner: TypeEnvOwner,
	) -> Result<(), SolverError> {
		// The clauses are written in the declaration's frame, about its own
		// subject; the use supplies that frame's arguments and the subject.
		// The arguments are owned: the proof interns while it reads them.
		let (clauses, root, frame, arguments): (_, _, _, Box<[TypeIndex]>) =
			match requirements {
				BoundRequirements::Parameter {
					env,
					index,
					arguments,
				} => (
					self.param_bounds[usize::from(env)][index].clauses,
					self.type_envs.param_types(env)[index],
					env,
					self.types.list(arguments).into(),
				),
				BoundRequirements::AssociatedType {
					declaration,
					trait_index,
					receiver,
				} => {
					let Some(signature) =
						&self.assoc_types[usize::from(declaration)]
					else {
						return Err(SolverError::Pending);
					};
					let env = self.traits[usize::from(trait_index)].env;
					let root = self.types.intern(Type::AssocTypeProjection {
						base: self.type_envs.param_types(env)[0],
						trait_index,
						assoc_type_index: declaration,
					});
					(signature.clauses, root, env, Box::new([receiver]))
				}
			};
		let mut failures = Vec::new();
		if self.satisfies_clauses(
			assumption_context,
			clauses,
			(root, argument.inner),
			(frame, &arguments),
			Some(&mut failures),
			None,
		)? {
			return Ok(());
		}
		for failure in failures {
			let diagnostic = match failure {
				UnsatisfiedClause::Trait {
					subject,
					trait_index,
					source,
				} => self.report_trait_bound_violation(
					reference.file_id,
					Spanned {
						inner: subject,
						span: argument.span,
					},
					trait_index,
					source,
					owner,
				),
				UnsatisfiedClause::Equality {
					projection,
					found,
					expected,
					source,
				} => self.report_equality_mismatch(
					SourceSpan::new(reference.file_id, argument.span),
					projection,
					found,
					expected,
					source,
					owner,
				),
			};
			self.diagnostics.push(diagnostic);
		}
		Err(SolverError::Poisoned)
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
		let declared_anywhere = (0..self.defs.traits.len()).any(|index| {
			self.defs
				.declared_trait_member(TraitIdx::new(index as u32), key)
				.is_some()
		});
		let normalized = match self.normalize(
			assumption_context,
			projection,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
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
		match ImplTarget::from_type(self.types.resolve(normalized)) {
			Some(target) => {
				for &(trait_index, _) in
					self.impl_dispatch.trait_candidates(target)
				{
					if self
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
				self.types.resolve(normalized),
				Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
			) =>
			{
				let declared = self.clause_tables().declared_traits(
					&self.types,
					normalized,
					self.solver.state.recursion_budget,
				);
				match TypeContext::select_declared_member(
					self.defs, declared, key,
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
				.resolve(self.defs.traits[usize::from(trait_index)].name.inner)
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
					// An impl has no name to point at; its bound is shown.
					match owner.name(self.defs) {
						Some(name) => format!(
							"required by a bound in `{}`",
							self.strings.resolve(name.inner).unwrap()
						),
						None => "required by this bound".to_owned(),
					},
				),
			)
	}

	/// rustc's E0271: the projection a bound's equality names has another
	/// value. The written equality is shown, since that is what the value
	/// failed.
	fn report_equality_mismatch(
		&self,
		reference: SourceSpan,
		projection: TypeIndex,
		found: TypeIndex,
		expected: TypeIndex,
		source: BindingRef,
		owner: TypeEnvOwner,
	) -> Diagnostic<FileId> {
		let formatter = self.type_formatter();
		let (projection, found, expected) = (
			formatter.display_type(projection),
			formatter.display_type(found),
			formatter.display_type(expected),
		);
		let ast::Spanned { span, .. } = match self.bounds.binding(source).kind {
			BindingRequirement::Equals(value) => value,
			BindingRequirement::Bound(_) => {
				unreachable!("an equality clause comes from a written equality")
			}
		};
		let written =
			SourceSpan::new(self.bounds.span(source.bound).file_id, span);
		Diagnostic::error()
			.with_code(DiagnosticCode::AssocTypeEqualityMismatch.code())
			.with_message(format!(
				"type mismatch resolving `{projection} == {expected}`"
			))
			.with_label(reference.primary_label().with_message(format!(
				"expected `{expected}`, found `{found}`"
			)))
			.with_label(written.secondary_label().with_message(
				match owner.name(self.defs) {
					Some(name) => format!(
						"required by this equality in `{}`",
						self.strings.resolve(name.inner).unwrap()
					),
					None => "required by this equality".to_owned(),
				},
			))
	}
}

/// What a path segment written with type arguments names when it can
/// never declare parameters. An impl's `Self` has its own report, which
/// shows the target the impl names.
pub(super) enum TypeArgsNotAllowedOn<'a> {
	/// A namespace a path passes through, an enum, a global, a memory, an
	/// associated type or an intrinsic type alias.
	Declaration(DefKind),
	/// A generic parameter or a trait's `Self`, and the declaration whose
	/// frame declares it.
	TypeParam {
		owner: TypeEnvOwner,
		name: &'a Spanned<SymbolU32>,
	},
}

/// Type arguments on a name that never takes any, as opposed to a wrong
/// count for one that declares a parameter list.
pub(super) fn report_type_args_not_allowed(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	segment: &ast::PathSegment,
	target: TypeArgsNotAllowedOn<'_>,
) -> Diagnostic<FileId> {
	let (noun, declared_at) = match target {
		TypeArgsNotAllowedOn::Declaration(kind) => {
			(kind.noun(), kind.declared_at(defs))
		}
		TypeArgsNotAllowedOn::TypeParam { owner, name } => (
			if name.inner == Keyword::SelfPascal.symbol() {
				"self type"
			} else {
				"type parameter"
			},
			Some(SourceSpan::new(owner.file_id(defs), name.span)),
		),
	};
	let name = strings.resolve(segment.ident.inner).unwrap();
	let (first, last) = (
		segment.type_args.first().unwrap(),
		segment.type_args.last().unwrap(),
	);
	let mut labels = vec![
		SourceSpan::new(
			file_id,
			TextSpan::new(first.span().start, last.span().end),
		)
		.primary_label()
		.with_message(format!(
			"type argument{} not allowed",
			if segment.type_args.len() == 1 {
				""
			} else {
				"s"
			}
		)),
		SourceSpan::new(file_id, segment.ident.span)
			.secondary_label()
			.with_message(format!("not allowed on {noun} `{name}`")),
	];
	if let Some(declared_at) = declared_at {
		labels.push(
			declared_at
				.secondary_label()
				.with_message(format!("{noun} `{name}` defined here")),
		);
	}
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeArgumentsNotAllowed.code())
		.with_message(format!(
			"type arguments are not allowed on {noun} `{name}`"
		))
		.with_labels(labels)
		.with_note(format!(
			"{noun} `{name}` has no generic parameters; write `{name}` alone"
		))
}

/// A wrong number of type arguments for a declaration with its own
/// parameter list, possibly empty: a struct, a function or a type alias.
fn report_type_arg_count_mismatch(
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	file_id: FileId,
	segment: &ast::PathSegment,
	owner: TypeEnvOwner,
	params: &[Spanned<SymbolU32>],
) -> Diagnostic<FileId> {
	let (noun, name) = (owner.noun(), segment.ident.inner);
	let declaration = owner.name(defs).map(|declared| {
		(SourceSpan::new(owner.file_id(defs), declared.span), params)
	});
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
		let label = SourceSpan::new(file_id, arg.span()).secondary_label();
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
				SourceSpan::new(declared_at.file_id, param.span)
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
	use crate::tir::solver::Solver;
	use crate::tir::types::Type;
	use crate::vfs;

	/// Parses `source` (playing the stdlib's own role, same reasoning as
	/// `signatures::tests::source_graph`), sweeps every registered item's
	/// signature, then hands the live `TypeContext` to `f`. Nothing borrowed
	/// here (`graph`, `defs`, `ast_nodes`, `diagnostics`) may escape this
	/// call; only `f`'s own, owned return value does.
	fn with_resolved<R>(
		source: &str,
		f: impl FnOnce(&mut TypeContext) -> R,
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
		let mut solver = Solver::new(defs.constants.len());
		let mut builder = TypeContext::new(
			&mut diagnostics,
			&mut resolutions,
			&mut graph.strings,
			&mut solver,
			&graph.files,
			&defs,
			&ast_nodes,
			&impl_dispatch,
		);
		builder.sweep();
		assert!(builder.diagnostics.is_empty(), "{:?}", builder.diagnostics);

		f(&mut builder)
	}

	/// Resolves `path` (`::`-separated) as a `tier`-tier path from the root
	/// namespace — same mechanism a written bound or type actually uses,
	/// mirroring `signatures::tests::TestCase::resolve`.
	fn resolve(builder: &TypeContext, tier: Tier, path: &str) -> DefKind {
		let root = Scope::Package(builder.defs.root_package);
		let file_id = builder.defs.namespaces.file_id(root.into());

		let segments: Box<[ast::PathSegment]> = path
			.split("::")
			.map(|segment| ast::PathSegment {
				ident: Spanned {
					inner: builder
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
			builder.strings,
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

	fn trait_index(builder: &TypeContext, path: &str) -> TraitIdx {
		let DefKind::Trait(trait_index) = resolve(builder, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a trait");
		};
		trait_index
	}

	/// The `TraitIndex` of `path`'s compiler-generated backing trait — what
	/// a `T: <path>` bound naming this typeset actually resolves to. See
	/// `TypeSetSignature`'s own doc comment.
	fn typeset_trait_index(builder: &TypeContext, path: &str) -> TraitIdx {
		let DefKind::TypeSet(typeset_index) =
			resolve(builder, Tier::Type, path)
		else {
			panic!("expected `{path}` to be a typeset");
		};
		builder.defs.typesets[usize::from(typeset_index)].trait_index
	}

	/// `path`'s own `TypeIndex` — a non-generic struct only(a generic
	/// struct's instantiated `TypeIndex` needs type-argument resolution,
	/// which isn't implemented yet — see `impls.rs::resolve_impl_target`).
	fn struct_type(builder: &mut TypeContext, path: &str) -> TypeIndex {
		let DefKind::Struct(struct_index) = resolve(builder, Tier::Type, path)
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
		function_path: &str,
		param_index: u32,
	) -> TypeIndex {
		let DefKind::Function(function_index) =
			resolve(builder, Tier::Value, function_path)
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
			|builder| {
				let foo = trait_index(builder, "Foo");
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
			|builder| {
				let foo = trait_index(builder, "Foo");
				let s = struct_type(builder, "S");
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
			|builder| {
				let bar = trait_index(builder, "Bar");
				let s = struct_type(builder, "S");
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
			|builder| {
				let nums = typeset_trait_index(builder, "Nums");
				let s = struct_type(builder, "S");
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
			|builder| {
				let bound = trait_index(builder, "Bound");
				let t = generic_param_type(builder, "target", 0);
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
			|builder| {
				let other = trait_index(builder, "Other");
				let t = generic_param_type(builder, "target", 0);
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
			|builder| {
				let super_trait = trait_index(builder, "Super");
				let t = generic_param_type(builder, "target", 0);
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
