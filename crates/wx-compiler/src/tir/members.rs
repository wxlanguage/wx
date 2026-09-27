//! Type-relative member resolution: given an already-resolved type
//! (concrete or abstract), find a function/const/associated-type member by
//! name. The companion to `paths.rs`, which only ever resolves *names*
//! through the namespace graph — this module picks up exactly where that
//! one's own doc comment says it has to stop: once a segment names
//! something that doesn't own a namespace, continuing needs impl dispatch
//! (`impls.rs`) or bound projection instead, neither of which involves the
//! namespace graph, `use`, or `Visibility` at all.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

use crate::ast::{self, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::types::TypeEnvOwner;
use crate::vfs::FileId;

use super::bounds::{ImpliedTraitBound, report_not_an_associated_type};
use super::defs::{
	AssocTypeIdx, BindingKey, BindingNamespace, DefinitionRegistry,
	InherentImplIdx, MemberKind, TraitIdx, TraitImplIdx,
};
use super::impls::ImplTarget;
use super::signatures::{
	QueryInfo, SignatureBuilder, SignatureLocation, SignatureStatus,
};
use super::types::{Type, TypeIndex};

/// What a type-relative member lookup found.
pub(super) enum TypeMemberLookup {
	NotFound,
	Found(TypeMemberTarget),
	/// Two or more *unrelated* traits each provide this name for this
	/// receiver — inherent-vs-trait precedence never lands here (inherent
	/// always wins outright, checked before any trait candidate at all), so
	/// this only ever holds trait-sourced candidates.
	Ambiguous(Box<[TypeMemberTarget]>),
}

pub(super) struct TypeMemberTarget {
	/// Carries the index into the member's definition arena.
	pub(super) kind: MemberKind,
	pub(super) source: MemberSource,
}

pub(super) enum MemberSource {
	Inherent(InherentImplIdx),
	/// A concrete `impl Trait for Type` provides (or overrides) this member.
	TraitImpl(TraitIdx, TraitImplIdx),
	/// No impl overrides it for this concrete type — the trait's own
	/// declaration applies as-is. Whether that declaration has a body is
	/// not this lookup's concern: an impl missing a required override is an
	/// ill-formed program, caught later by trait-conformance checking (the
	/// last checking phase, run only once every body is resolved) — not
	/// something name resolution needs to gate on. Mirrors rustc, which
	/// never reports an error at an access site for an incorrectly
	/// implemented trait member, only at the `impl` block that's missing
	/// it.
	TraitDefault(TraitIdx),
	/// Receiver is abstract (`TypeParam`/`AssocTypeProjection`): resolved
	/// through one of its own bounds, not a concrete impl at all. Concrete
	/// dispatch is deferred to monomorphization (mirrors the existing
	/// `GenericMethodCall`/`AbstractConstAccess` shape).
	Bound(TraitIdx),
}

/// How `required_trait` applies to a receiver, per `find_trait_impl`.
pub(super) enum TraitImplLookup {
	/// Concrete receiver, with a registered `impl required_trait for
	/// receiver` (`impls.rs`'s dispatch) — `TraitImplIdx` names it, in
	/// case it overrides the member being looked up.
	Concrete(TraitImplIdx),
	/// Abstract receiver (`TypeParam`/`AssocTypeProjection`) whose implied
	/// bounds (or, inside the trait itself, its own reflexive `Self`
	/// bound) include `required_trait`. Concrete dispatch is deferred to
	/// monomorphization, so there's no impl index to name yet.
	Abstract,
}

impl SignatureBuilder<'_, '_> {
	/// Resolves `name` (in binding tier `tier` — `Value` for a
	/// function/const, `Type` for an associated type) as a member of
	/// `receiver`. `reference` is the span of whatever named `receiver` in
	/// the first place — threaded through to `ensure_assoc_type_signature`,
	/// the one path below that can force another item's signature and so
	/// needs a real "why" to attach to a cycle diagnostic.
	pub(super) fn resolve_type_member(
		&mut self,
		receiver: TypeIndex,
		tier: BindingNamespace,
		name: SymbolU32,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		let key = BindingKey::new(tier, name);
		match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => self.resolve_concrete_member(target, key),
			None => self.resolve_bound_member(receiver, key, reference),
		}
	}

	/// Walks `segments` as member lookups off of `current` — a struct
	/// field, associated type, or method, resolved by name rather than
	/// through the namespace graph. Shared by `resolve_type`'s own `Path`
	/// arm (for whatever's left once its namespace-tier prefix is
	/// consumed), its `Grouped` arm (`<T>::Item`, which has no namespace-
	/// tier prefix at all — `current` starts as `T` itself), and its
	/// `QualifiedPath` arm (for whatever's left after the first, trait-
	/// qualified segment).
	pub(super) fn resolve_type_member_path(
		&mut self,
		file_id: FileId,
		mut current: TypeIndex,
		segments: &[ast::PathSegment],
	) -> TypeIndex {
		for segment in segments {
			if !segment.type_args.is_empty() {
				todo!(
					"generic args on a type-relative path segment aren't implemented yet"
				)
			}
			match self.resolve_type_member(
				current,
				BindingNamespace::Type,
				segment.ident.inner,
				SourceSpan::new(file_id, segment.ident.span),
			) {
				TypeMemberLookup::Found(member) => {
					current = self.project_type_member(current, member);
				}
				TypeMemberLookup::NotFound => {
					self.diagnostics.push(report_no_such_type_member(
						file_id,
						self.strings,
						segment.ident,
					));
					return TypeIndex::ERROR;
				}
				TypeMemberLookup::Ambiguous(candidates) => {
					self.diagnostics.push(report_ambiguous_type_member(
						file_id,
						self.strings,
						self.defs,
						segment.ident,
						&candidates,
					));
					return TypeIndex::ERROR;
				}
			}
		}
		current
	}

	/// Turns a resolved member lookup into the next `current` type in a
	/// path walk — `base` is whatever `member` was looked up on. Shared by
	/// `resolve_type_member_path`'s per-segment loop and `QualifiedPath`'s
	/// one-off first segment, which resolves its member a different way
	/// (`resolve_trait_qualified_member`, not `resolve_type_member`) but
	/// turns the result into a type the same way.
	pub(super) fn project_type_member(
		&mut self,
		base: TypeIndex,
		member: TypeMemberTarget,
	) -> TypeIndex {
		match member.kind {
			MemberKind::AssociatedType(assoc_type_index) => match member.source {
				MemberSource::Bound(trait_index) => {
					self.types.intern(Type::AssocTypeProjection {
						trait_index,
						assoc_type_index,
						base,
					})
				}
				MemberSource::Inherent(_)
				| MemberSource::TraitImpl(..)
				| MemberSource::TraitDefault(_) => {
					todo!(
						"associated-type projection off a concrete receiver isn't implemented yet — needs TraitImplAssocType's own signature resolution"
					)
				}
			},
			// Every caller resolves in `BindingNamespace::Type` — a
			// Function/Method/Constant is Value-tier, so `bindings` (keyed
			// by tier) can never match one here.
			MemberKind::Function(_)
			| MemberKind::Method(_)
			| MemberKind::Constant(_) => unreachable!(
				"a Type-tier lookup cannot resolve to a Value-tier member"
			),
		}
	}

	/// Resolves `<receiver as required_trait>::name` — the first, trait-
	/// qualified segment of a `QualifiedPath`. The rest of a multi-segment
	/// qualified path (`<T as Trait>::Item::Next`) continues through the
	/// ordinary `resolve_type_member_path`, same as `Grouped`/`Path` — only
	/// the first segment is ever qualified, since a qualification pins down
	/// *which* trait provides that one name, and everything after it is
	/// projected off whatever that named.
	pub(super) fn resolve_trait_qualified_member(
		&mut self,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		tier: BindingNamespace,
		name: Spanned<SymbolU32>,
		file_id: FileId,
	) -> Result<TypeMemberTarget, ()> {
		let key = BindingKey::new(tier, name.inner);
		let trait_def = &self.defs.traits[usize::from(required_trait)];
		let Some(&member_index) = trait_def.bindings.get(&key) else {
			self.diagnostics.push(report_not_an_associated_type(
				file_id,
				self.strings,
				name,
				trait_def.name.inner,
			));
			return Err(());
		};
		let declared_kind = trait_def.members[usize::from(member_index)].kind;

		let found =
			self.find_trait_impl(receiver, required_trait, file_id, name.span)?;
		Ok(match found {
			TraitImplLookup::Concrete(impl_index) => {
				let impl_def = &self.defs.trait_impls[usize::from(impl_index)];
				match impl_def.bindings.get(&key) {
					Some(&member_index) => TypeMemberTarget {
						kind: impl_def.members[usize::from(member_index)].kind,
						source: MemberSource::TraitImpl(
							required_trait,
							impl_index,
						),
					},
					None => TypeMemberTarget {
						kind: declared_kind,
						source: MemberSource::TraitDefault(required_trait),
					},
				}
			}
			TraitImplLookup::Abstract => TypeMemberTarget {
				kind: declared_kind,
				source: MemberSource::Bound(required_trait),
			},
		})
	}

	/// Finds how `required_trait` applies to `receiver`, if at all — a
	/// concrete registered impl, or (for an abstract receiver) membership
	/// in its own implied bounds. Decoupled from looking up any particular
	/// member, so it's exactly as usable wherever else "does `receiver`
	/// have an impl/bound for `required_trait`" needs answering, not only
	/// for `resolve_trait_qualified_member`'s own use. Not a conformance
	/// check: it doesn't care whether that impl/bound actually provides
	/// everything the trait requires, only whether one exists at all —
	/// completeness is `check_trait_conformance`'s own, separate job.
	pub(super) fn find_trait_impl(
		&mut self,
		receiver: TypeIndex,
		required_trait: TraitIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TraitImplLookup, ()> {
		let found = match ImplTarget::from_type(self.types.resolve(receiver)) {
			Some(target) => {
				self.impl_dispatch.trait_candidates(target).iter().find_map(
					|&(trait_index, impl_index)| {
						(trait_index == required_trait)
							.then_some(TraitImplLookup::Concrete(impl_index))
					},
				)
			}
			None => match self.types.resolve(receiver) {
				Type::TypeParam { env, param_index } => {
					let is_reflexive = matches!(
						self.type_envs.frame_owner(*env),
						TypeEnvOwner::Trait(trait_index)
							if trait_index == required_trait
					);
					let implied = &self.param_bounds[usize::from(*env)]
						[*param_index as usize]
						.implied_bounds;
					(is_reflexive
						|| implied
							.iter()
							.any(|bound| bound.trait_index == required_trait))
					.then_some(TraitImplLookup::Abstract)
				}
				Type::AssocTypeProjection {
					assoc_type_index, ..
				} => {
					let assoc_type_index = *assoc_type_index;
					if self
						.ensure_assoc_type_signature(
							assoc_type_index,
							SourceSpan::new(file_id, span),
						)
						.is_err()
					{
						// Already diagnosed (a cycle) — don't pile the
						// "doesn't implement this trait" diagnostic below
						// on top of it.
						return Err(());
					}
					self.assoc_types[usize::from(assoc_type_index)]
						.as_ref()
						.expect("trait associated type signature is resolved")
						.implied_bounds
						.iter()
						.any(|bound| bound.trait_index == required_trait)
						.then_some(TraitImplLookup::Abstract)
				}
				_ => None,
			},
		};
		found.ok_or_else(|| {
			let diagnostic = self.report_type_does_not_implement_trait(
				file_id,
				span,
				receiver,
				required_trait,
			);
			self.diagnostics.push(diagnostic);
		})
	}

	/// Same code and wording as `check_assoc_type_value`'s own
	/// `report_trait_bound_violation` (mirroring rustc's `E0277` for this
	/// same case: `the trait bound `Foo: Bar` is not satisfied`) — this is
	/// that same condition, just reached with no declared bound clause to
	/// point a "required by a bound in `X`" secondary label at, since a
	/// qualified path's `as Trait` isn't one.
	fn report_type_does_not_implement_trait(
		&self,
		file_id: FileId,
		span: TextSpan,
		receiver: TypeIndex,
		required_trait: TraitIdx,
	) -> Diagnostic<FileId> {
		let receiver_name = self.type_formatter().display_type(receiver);
		let trait_name = self
			.strings
			.resolve(self.defs.traits[usize::from(required_trait)].name.inner)
			.unwrap();
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the trait bound `{receiver_name}: {trait_name}` is not satisfied"
			))
			.with_label(
				SourceSpan::new(file_id, span).primary_label().with_message(
					format!(
						"the trait `{trait_name}` is not implemented for `{receiver_name}`"
					),
				),
			)
	}

	fn resolve_concrete_member(
		&mut self,
		target: ImplTarget,
		key: BindingKey,
	) -> TypeMemberLookup {
		// No forcing needed here: ImplDispatch was built from declarations
		// before signature resolution began.

		// Inherent always wins outright — no trait candidate is even
		// consulted once one matches.
		for &index in self.impl_dispatch.inherent_candidates(target) {
			let impl_def = &self.defs.inherent_impls[usize::from(index)];
			if let Some(&member_index) = impl_def.bindings.get(&key) {
				let kind = impl_def.members[usize::from(member_index)].kind;
				return TypeMemberLookup::Found(TypeMemberTarget {
					kind,
					source: MemberSource::Inherent(index),
				});
			}
		}

		let mut candidates = Vec::new();
		for &(trait_index, impl_index) in
			self.impl_dispatch.trait_candidates(target)
		{
			let impl_def = &self.defs.trait_impls[usize::from(impl_index)];
			if let Some(&member_index) = impl_def.bindings.get(&key) {
				let kind = impl_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::TraitImpl(trait_index, impl_index),
				});
				continue;
			}
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				let kind = trait_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::TraitDefault(trait_index),
				});
			}
			// Else: this trait doesn't declare `name` at all — not a
			// candidate, nothing to record.
		}
		Self::classify(candidates)
	}

	fn resolve_bound_member(
		&mut self,
		receiver: TypeIndex,
		key: BindingKey,
		reference: SourceSpan,
	) -> TypeMemberLookup {
		match self.types.resolve(receiver) {
			Type::TypeParam { env, param_index } => self
				.candidates_from_implied(
					&self.param_bounds[usize::from(*env)]
						[*param_index as usize]
						.implied_bounds,
					key,
					match self.type_envs.frame_owner(*env) {
						TypeEnvOwner::Trait(trait_index) => Some(trait_index),
						_ => None,
					},
				),
			Type::AssocTypeProjection {
				assoc_type_index, ..
			} => {
				let assoc_type_index = *assoc_type_index;
				if self
					.ensure_assoc_type_signature(assoc_type_index, reference)
					.is_err()
				{
					return TypeMemberLookup::NotFound;
				}
				self.candidates_from_implied(
					&self.assoc_types[usize::from(assoc_type_index)]
						.as_ref()
						.expect("trait associated type signature is resolved")
						.implied_bounds,
					key,
					None,
				)
			}
			// Error/Infer/anything else `ImplTarget` also can't bucket and
			// that isn't one of the two abstract shapes — nothing to look
			// a member up on.
			_ => TypeMemberLookup::NotFound,
		}
	}

	/// Turns an already-merged implied set into a lookup result — shared
	/// between all three receiver shapes `resolve_bound_member` handles.
	/// Purely identity: which member definition this name names. Whether the
	/// combination's `where { .. }` bindings for it actually agree
	/// (`MergedBindingKind::Conflicting`, already diagnosed once by
	/// `union_trait_bound`) is a fact about this associated type's *value*,
	/// not about its identity — `A::X` is `A::X` regardless of whether `B`
	/// and `C` agree what it equals — so it's irrelevant here. It only
	/// matters to whatever eventually normalizes/substitutes this
	/// projection, which isn't this function's job.
	fn candidates_from_implied(
		&self,
		bounds: &[ImpliedTraitBound],
		key: BindingKey,
		reflexive: Option<TraitIdx>,
	) -> TypeMemberLookup {
		let mut candidates = Vec::new();
		for (trait_index, _bound) in reflexive
			.into_iter()
			.map(|index| (index, None))
			.chain(bounds.iter().map(|bound| (bound.trait_index, Some(bound))))
		{
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			if let Some(&member_index) = trait_def.bindings.get(&key) {
				let kind = trait_def.members[usize::from(member_index)].kind;
				candidates.push(TypeMemberTarget {
					kind,
					source: MemberSource::Bound(trait_index),
				});
			}
		}
		Self::classify(candidates)
	}

	/// Forces `assoc_type_index`'s own signature to be resolved. The only
	/// failure is a cycle, diagnosed here once — `CycleReported` means
	/// another call already did.
	pub(super) fn ensure_assoc_type_signature(
		&mut self,
		assoc_type_index: AssocTypeIdx,
		requested_at: SourceSpan,
	) -> Result<(), ()> {
		let def_id =
			self.defs.assoc_types[usize::from(assoc_type_index)].def_id;
		match self.ensure_signature(QueryInfo {
			def_id,
			requested_at: Some(requested_at),
		}) {
			SignatureStatus::Resolved(SignatureLocation::AssocType(
				..,
			)) => Ok(()),
			SignatureStatus::Resolved(_) => unreachable!(
				"an AssociatedType member's DefId always resolves to SignatureLocation::AssocType"
			),
			SignatureStatus::Cycle => {
				let diagnostic =
					self.report_cyclic_assoc_type_bound(def_id, requested_at);
				self.diagnostics.push(diagnostic);
				Err(())
			}
			SignatureStatus::CycleReported => Err(()),
		}
	}

	fn classify(mut candidates: Vec<TypeMemberTarget>) -> TypeMemberLookup {
		match candidates.len() {
			0 => TypeMemberLookup::NotFound,
			1 => TypeMemberLookup::Found(candidates.pop().unwrap()),
			_ => TypeMemberLookup::Ambiguous(candidates.into_boxed_slice()),
		}
	}
}

fn report_no_such_type_member(
	file_id: FileId,
	strings: &StringInterner,
	name: Spanned<SymbolU32>,
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	Diagnostic::error()
		.with_code(DiagnosticCode::NotATraitMember.code())
		.with_message(format!(
			"no associated type named `{name_str}` found for this type"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label())
}

/// `candidates` never holds a `MemberSource::Inherent` entry — inherent
/// always wins outright in `resolve_concrete_member`, before any trait
/// candidate is even gathered, so nothing ever reaches `Ambiguous` through
/// it.
fn report_ambiguous_type_member(
	file_id: FileId,
	strings: &StringInterner,
	defs: &DefinitionRegistry,
	name: Spanned<SymbolU32>,
	candidates: &[TypeMemberTarget],
) -> Diagnostic<FileId> {
	let name_str = strings.resolve(name.inner).unwrap();
	let mut diagnostic = Diagnostic::error()
		.with_code(DiagnosticCode::AmbiguousTraitMember.code())
		.with_message(format!(
			"`{name_str}` is ambiguous between multiple traits"
		))
		.with_label(SourceSpan::new(file_id, name.span).primary_label());
	for candidate in candidates {
		let trait_index = match candidate.source {
			MemberSource::TraitImpl(trait_index, _)
			| MemberSource::TraitDefault(trait_index)
			| MemberSource::Bound(trait_index) => trait_index,
			MemberSource::Inherent(_) => continue,
		};
		let trait_name = strings
			.resolve(defs.traits[usize::from(trait_index)].name.inner)
			.unwrap();
		diagnostic =
			diagnostic.with_note(format!("provided by trait `{trait_name}`"));
	}
	diagnostic
}
