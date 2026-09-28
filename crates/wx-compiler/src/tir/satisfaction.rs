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
use super::defs::{AssocTypeIdx, DefinitionRegistry, TraitIdx};
use super::impls::ImplTarget;
use super::signatures::SignatureBuilder;
use super::types::{Type, TypeEnvIdx, TypeIndex, TypeParam};
use crate::ast::{Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

impl SignatureBuilder<'_, '_> {
	/// Does `ty` satisfy `trait_index`? `reference` is the span of whatever
	/// is being checked against this bound, threaded through to
	/// `ensure_assoc_type_bounds` for its own cycle diagnostic, same role
	/// it plays in `resolve_type_member`/`resolve_bound_member`.
	///
	/// `Error`/`Infer` satisfy everything — both are already diagnosed
	/// wherever they were produced, so failing a bound check here too would
	/// only cascade that one root cause into every bound that happens to
	/// mention it. Same reasoning applies to a projection that fails to
	/// normalize below: normalization already diagnosed that failure.
	///
	/// An abstract receiver tries its effective bound facts first — cheap,
	/// and the common case for a bare generic parameter — before falling
	/// back to normalizing and dispatching structurally, the same order
	/// `find_trait_impl` (members.rs) uses. Without that fallback, a
	/// projection that reduces to a concrete type satisfying the trait
	/// (`U::Item` where `U: Value where { Item = i32 }` and `i32: Marker`)
	/// was rejected outright merely for not having `Marker` as a directly
	/// asserted bound.
	pub(super) fn type_satisfies_trait(
		&mut self,
		ty: TypeIndex,
		trait_index: TraitIdx,
		reference: SourceSpan,
	) -> bool {
		if matches!(self.types.resolve(ty), Type::Error | Type::Infer) {
			return true;
		}
		if matches!(
			self.types.resolve(ty),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			if self.prepare_effective_bounds(ty, reference).is_err() {
				return true;
			}
			if self.has_effective_trait(ty, trait_index) {
				return true;
			}
		}
		let ty = self.normalize_head(ty, reference);
		if ty == TypeIndex::ERROR {
			return true;
		}
		let Some(target) = ImplTarget::from_type(self.types.resolve(ty)) else {
			return false;
		};
		let candidate =
			self.impl_dispatch.trait_candidates(target).iter().find_map(
				|&(candidate, impl_index)| {
					(candidate == trait_index).then_some(impl_index)
				},
			);
		candidate.is_some_and(|impl_index| {
			self.match_trait_impl_candidate(impl_index, ty, reference)
				.is_some()
		})
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
	/// Diagnoses and returns `TypeIndex::ERROR` for the first bound `value`
	/// fails; `value.inner` unchanged if every bound is satisfied, or if
	/// the declaration turned out cyclic (already diagnosed by the force
	/// above — same shortcut `type_satisfies_trait` takes for `Error`/
	/// `Infer`, rather than piling a second failure on top).
	///
	/// Re-indexes `self.assoc_types[declared_assoc_type]` fresh on each
	/// iteration instead of holding a slice across the loop, so the
	/// `&Copy` pair it needs (`trait_index`, `source`) is extracted in a
	/// scope that ends before the `&mut self` call below — no allocation,
	/// no cloning the bound list.
	pub(super) fn check_assoc_type_value(
		&mut self,
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
		let len = self.assoc_types[usize::from(declared_assoc_type)]
			.as_ref()
			.expect("trait associated type signature is resolved")
			.facts
			.current()
			.len();
		for i in 0..len {
			let (trait_index, bound_id) = {
				let bound = &self.assoc_types[usize::from(declared_assoc_type)]
					.as_ref()
					.expect("trait associated type signature is resolved")
					.facts
					.current()[i];
				(bound.trait_index, bound.source)
			};
			if !self.type_satisfies_trait(value.inner, trait_index, reference) {
				let diagnostic = self.report_trait_bound_violation(
					file_id,
					value,
					trait_index,
					bound_id,
					owner,
				);
				self.diagnostics.push(diagnostic);
				return TypeIndex::ERROR;
			}
		}
		value.inner
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
	/// list, is poisoned when any of them fails.
	pub(super) fn resolve_type_args(
		&mut self,
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
		for (index, arg) in args.iter().copied().enumerate() {
			let bounds: Vec<(TraitIdx, BoundId)> = self
				.implied_bounds(params_env, index as u32)
				.iter()
				.map(|bound| (bound.trait_index, bound.source))
				.collect();

			let mut satisfied = true;
			let reference = SourceSpan::new(file_id, arg.span);
			for (trait_index, bound_id) in bounds {
				if !self.type_satisfies_trait(arg.inner, trait_index, reference)
				{
					satisfied = false;
					let diagnostic = self.report_trait_bound_violation(
						file_id,
						arg,
						trait_index,
						bound_id,
						owner,
					);
					self.diagnostics.push(diagnostic);
				}
			}
			result.push(if satisfied {
				arg.inner
			} else {
				TypeIndex::ERROR
			});
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
				self.bounds
					.get(bound_id)
					.span
					.secondary_label()
					.with_message(format!(
						"required by a bound in `{}`",
						self.strings
							.resolve(owner.name(self.defs).unwrap().inner)
							.unwrap()
					)),
			)
	}
}

/// `params` is the target's own frame, straight from `TypeEnvArena` — reads
/// each `EnvParam`'s own (already `pub(super)`) `name` field directly rather
/// than going through a single-index accessor per name/span, since nothing
/// here needs `param`'s own resolved `ty` or `accesses`.
fn report_type_arg_count_mismatch(
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
			label.with_message(format!(
				"supplied {found} generic argument{}",
				plural(found)
			))
		} else {
			label
		});
	}

	let owner_str = strings.resolve(owner_name.inner).unwrap();
	labels.push(
		SourceSpan::new(owner_file_id, owner_name.span)
			.secondary_label()
			.with_message(format!(
				"defined here, with {expected} generic parameter{}",
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
	/// `signatures::tests::TestCase::new` — `ensure_signature` isn't
	/// selective about which item kinds it drives, so real stdlib content
	/// would panic on whatever isn't implemented yet before a test even
	/// runs), forces every registered item's signature, then hands the
	/// live, fully-resolved `SignatureBuilder` to `f`.
	///
	/// `type_satisfies_trait` needs `&mut SignatureBuilder`, and that type
	/// borrows from the parsed AST (see `signatures.rs`'s own module doc
	/// comment on why), so — unlike `signatures::tests::TestCase`, which
	/// only ever keeps the frozen, lifetime-free `SignatureRegistry` around
	/// after building — nothing borrowed here (`graph`, `defs`, `ast_nodes`,
	/// `diagnostics`) is allowed to escape this call. Only `f`'s own, owned
	/// return value is.
	fn with_resolved<R>(
		source: &str,
		f: impl FnOnce(&mut SignatureBuilder, &vfs::CompilationUnit) -> R,
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
		let mut builder = SignatureBuilder::new(
			&mut diagnostics,
			&graph.strings,
			&defs,
			&ast_nodes,
			impl_dispatch,
		);
		for entry in ast_nodes.iter() {
			let _ = builder.ensure_signature(QueryInfo {
				def_id: entry.def_id,
				requested_at: None,
			});
		}
		assert!(builder.diagnostics.is_empty(), "{:?}", builder.diagnostics);

		f(&mut builder, &graph)
	}

	/// Resolves `path` (`::`-separated) as a `tier`-tier path from the root
	/// namespace — same mechanism a written bound or type actually uses,
	/// mirroring `signatures::tests::TestCase::resolve`.
	fn resolve(
		builder: &SignatureBuilder,
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
		builder: &SignatureBuilder,
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
		builder: &SignatureBuilder,
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
		builder: &mut SignatureBuilder,
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
		builder: &mut SignatureBuilder,
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
		builder: &SignatureBuilder,
		graph: &vfs::CompilationUnit,
	) -> SourceSpan {
		let root = graph.root_package.root_namespace();
		let file_id = builder.defs.namespaces[usize::from(root)].file_id;
		SourceSpan::new(file_id, TextSpan::new(0, 0))
	}

	#[test]
	fn error_and_infer_satisfy_everything() {
		with_resolved(
			indoc! {"
			trait Foo {}
		"},
			|builder, graph| {
				let reference = dummy_reference(builder, graph);
				let foo = trait_index(builder, graph, "Foo");
				assert!(builder.type_satisfies_trait(
					TypeIndex::ERROR,
					foo,
					reference
				));
				assert!(builder.type_satisfies_trait(
					TypeIndex::INFER,
					foo,
					reference
				));
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
				assert!(builder.type_satisfies_trait(s, foo, reference));
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
				assert!(!builder.type_satisfies_trait(s, bar, reference));
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
				assert!(builder.type_satisfies_trait(s, nums, reference));
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
				assert!(builder.type_satisfies_trait(t, bound, reference));
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
				assert!(!builder.type_satisfies_trait(t, other, reference));
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
				assert!(builder.type_satisfies_trait(
					t,
					super_trait,
					reference
				));
			},
		);
	}
}
