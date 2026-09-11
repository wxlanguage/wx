//! Unified bound checking: does a `subject` type satisfy a written set of
//! [`Bounds`] — trait membership, typeset membership, and the
//! `where { Assoc = T }` / `where { Assoc: Bound }` refinements, recursively?
//!
//! One operation, [`Builder::check_bounds`], behind every "does this type meet
//! these constraints" question that produces a diagnostic: declaration
//! validation, trait-conformance checking, and generic call sites. (Impl
//! *selection* stays separate — it needs a silent yes/no during dispatch, not
//! a diagnostic; see `ItemRegistry::type_args_satisfy_bounds`.)
//!
//! Four axes that are easy to conflate:
//!
//! * `origin` — *who* imposed the obligation: a function's `where` clause, a
//!   struct / type-alias / impl type parameter, or a trait's own
//!   `type Assoc: Bound` declaration. It names the "required by a bound in `X`"
//!   note and nothing else, and stays **constant** as the check recurses.
//! * `required` — the constraint set being checked *at this level*. It
//!   **shrinks** as recursion descends into a nested `where` binding: those
//!   fragments are borrowed sub-trees of the parent `Bounds` that no index
//!   names, which is why this is a parameter and not re-fetched from `origin`.
//! * `subject` — the type that must satisfy `required` here. Its type
//!   **changes** every level (`T` → `T::Assoc` → …) while its *place* — the
//!   code whose author can act on the violation — stays put, which is why it
//!   carries its own [`SourceSpan`] rather than borrowing a file id from the
//!   site.
//! * `type_args` — what the site being checked pinned `origin`'s type
//!   parameters to, in absolute index order (the same order
//!   `function_type_params_iter` yields, which is why a plain positional
//!   `substitute_type` is enough: `param_index` is absolute across the
//!   inherited-then-own chain). A `where { Assoc = U }` RHS is written in the
//!   *declaring* item's scope, so at a call site it has to be read through
//!   the call's inferred arguments before it means anything. **Empty** at a
//!   declaration site, where those parameters are still abstract and the RHS
//!   is checked as written; **constant** through recursion, since every
//!   nested `where` was written in that same scope.
//!
//! `Self`, when it appears in a `required` RHS and `type_args` did not
//! already cover it, resolves to the *enclosing* frame's subject: `origin`'s
//! own `Self` at the top (derived here, never passed in), then the parent
//! subject at each deeper level.
//!
//! The checker borrows only a [`TypeCtx`] (the interner it needs to
//! materialize substituted types, plus a read-only view of the item registry)
//! and the two graphs the type formatter needs — never the whole `Builder`.
//! It returns the violations as ready [`Diagnostic`]s instead of pushing them.
//! An **empty** result means "not disproved": a poisoned (`ERROR`) or
//! too-abstract input produces no diagnostic, exactly as a satisfied bound
//! does — deliberately, not "proved".

use super::*;

/// The type under check, together with where it was written. The file is
/// part of it because it is *not* always the site's own: a nested level's
/// subject is spanned by the callee's `where` clause, in the callee's file,
/// and pairing that span with the caller's file id points a label at a
/// meaningless offset in the wrong source.
#[derive(Clone, Copy)]
pub(super) struct Subject {
	ty: TypeIndex,
	at: SourceSpan,
}

impl Subject {
	pub(super) fn new(at: SourceSpan, ty: TypeIndex) -> Self {
		Self { ty, at }
	}

	/// A different type at the same place — a subject's concrete associated
	/// value, say, which is only ever named by the span that constrained it.
	fn with_type(self, ty: TypeIndex) -> Self {
		Self { ty, ..self }
	}
}

/// Everything about a check that is fixed for the whole traversal: which
/// namespace its type names are rendered from, who imposed the obligation,
/// and what the site pinned the declaring item's type parameters to. Only
/// `subject` and `required` change as `check_inner` recurses, which is
/// exactly why these three travel together. Note there is no file id here —
/// every span this reports carries its own (see [`Subject`] and
/// [`BoundChecker::origin_label`]).
#[derive(Clone, Copy)]
struct BoundSite<'a> {
	namespace: NamespaceIndex,
	origin: BoundOrigin,
	type_args: &'a [TypeIndex],
}

impl<'a> BoundSite<'a> {
	/// The same site, re-attributed to a bound written somewhere else — a
	/// trait's own `type Assoc: Bound`, whose RHS is in trait scope and so
	/// has no type arguments of this site's to read.
	fn attributed_to(self, origin: BoundOrigin) -> BoundSite<'a> {
		BoundSite {
			origin,
			type_args: &[],
			..self
		}
	}
}

/// Which declaration's written bounds are at issue. One fact, doing two jobs
/// that must never disagree: it *locates* the [`Bounds`] (see
/// [`BoundOrigin::bounds`]) and it names the "required by a bound in `X`"
/// label. Passing the two separately let a caller hand over bounds from one
/// declaration attributed to another.
#[derive(Clone, Copy)]
pub(super) enum BoundOrigin {
	/// Bounds on a type parameter of a function, struct, type alias, impl
	/// block, or a trait's own `Self` — which is where supertrait bounds
	/// live. `index` is absolute in `owner`'s visible chain (inherited first,
	/// then its own), the numbering `Type::TypeParam`'s `param_index` carries.
	TypeParam { owner: TypeParamOwner, index: usize },
	/// A trait's own `type Assoc: Bound` declaration. Rendered `Trait::Assoc`.
	TraitAssocType {
		trait_index: TraitIndex,
		name: SymbolU32,
	},
}

impl BoundOrigin {
	/// The written bounds this origin names. `None` only when the declaration
	/// itself is missing — an associated type the trait never declared, which
	/// is reported where that lookup fails, not here.
	pub(super) fn bounds(self, items: &ItemRegistry) -> Option<&Bounds> {
		match self {
			BoundOrigin::TypeParam { owner, index } => {
				Some(&items.type_param_info(owner, index).bounds)
			}
			BoundOrigin::TraitAssocType { trait_index, name } => items
				.trait_associated_type(trait_index, name)
				.map(|assoc| &assoc.bounds),
		}
	}
}

impl Builder<'_, '_> {
	/// Check `subject` against the bounds written at `origin`. See the module
	/// docs for what each argument means. Returns one [`Diagnostic`] per
	/// distinct violation; empty means nothing was disproved.
	///
	/// The bounds are fetched here rather than passed in, so no caller ever
	/// holds a `&Bounds` across this call — which is what used to force each
	/// of them to clone one out of the registry first.
	pub(super) fn check_bounds(
		&mut self,
		namespace: NamespaceIndex,
		subject: Subject,
		origin: BoundOrigin,
		type_args: &[TypeIndex],
	) -> Vec<Diagnostic<FileId>> {
		let items = &self.items;
		let Some(required) = origin.bounds(items) else {
			return Vec::new();
		};
		BoundChecker {
			ctx: TypeCtx {
				types: &mut self.types,
				items,
				interner: self.interner,
			},
			modules: &self.modules,
			packages: self.packages,
		}
		.run(
			BoundSite {
				namespace,
				origin,
				type_args,
			},
			subject,
			required,
		)
	}
}

pub(super) struct BoundChecker<'a> {
	ctx: TypeCtx<'a>,
	modules: &'a ModuleGraph,
	packages: &'a [PackageGraph],
}

impl<'a> BoundChecker<'a> {
	/// Build one from `Builder`'s fields directly. `Builder::check_bounds` is
	/// the convenient way in; this is for a caller that is already holding a
	/// `&ItemRegistry` and so cannot hand over `&mut self` — trait conformance
	/// walks the impl registry while it checks. `types`, `items` and
	/// `diagnostics` are disjoint fields, so the borrows coexist.
	pub(super) fn new(
		ctx: TypeCtx<'a>,
		modules: &'a ModuleGraph,
		packages: &'a [PackageGraph],
	) -> Self {
		BoundChecker {
			ctx,
			modules,
			packages,
		}
	}

	/// One associated-type *value* against the bounds its trait declares for
	/// it (`type Size: PointerSize where { .. }`). `self_ty` is what `Self`
	/// means inside those declared bounds — the impl's target.
	pub(super) fn check_assoc_value(
		&mut self,
		namespace: NamespaceIndex,
		trait_index: TraitIndex,
		name: SymbolU32,
		value: Subject,
		self_ty: TypeIndex,
	) -> Vec<Diagnostic<FileId>> {
		let site = BoundSite {
			namespace,
			origin: BoundOrigin::TraitAssocType { trait_index, name },
			// A declared bound's RHS is written in trait scope; the only
			// parameter it can name is `Self`, which `self_ty` supplies.
			type_args: &[],
		};
		let mut out = Vec::new();
		self.check_declared_bounds(
			site,
			trait_index,
			name,
			value,
			self_ty,
			&mut out,
		);
		out
	}
}

impl<'a> BoundChecker<'a> {
	fn run(
		&mut self,
		site: BoundSite<'_>,
		subject: Subject,
		required: &Bounds,
	) -> Vec<Diagnostic<FileId>> {
		let mut out = Vec::new();
		let enclosing_self =
			self.origin_self_ty(site.origin).unwrap_or(subject.ty);
		self.check_inner(
			site,
			subject,
			&required.traits,
			enclosing_self,
			&mut out,
		);
		out
	}

	/// Takes `traits` as a slice rather than a `&Bounds` because a nested
	/// level (see the recursive call below) borrows only the trait list a
	/// `where` binding carries, and there is no `Bounds` in the arena shaped
	/// that way to hand over.
	fn check_inner(
		&mut self,
		site: BoundSite<'_>,
		subject: Subject,
		traits: &[TraitBound],
		enclosing_self: TypeIndex,
		out: &mut Vec<Diagnostic<FileId>>,
	) {
		if subject.ty == TypeIndex::ERROR {
			return;
		}

		for trait_bound in traits.iter() {
			// Trait membership. A failure here poisons every refinement the
			// bound carries, so report it and move on rather than stacking a
			// "`T::Assoc` is wrong" error on a `T` that isn't even the right
			// trait.
			if !self.ctx.items.type_implements_trait(
				self.ctx.types,
				subject.ty,
				trait_bound.trait_index,
			) {
				out.push(self.report_missing_trait(site, subject, trait_bound));
				continue;
			}

			for binding in trait_bound.bindings.iter() {
				// A concrete subject answers from its impl; an abstract one
				// answers from its own declared bounds, which are the whole
				// truth about it (`fn g<U: Has where { Item = bool }>` fixes
				// `U::Item` for the whole of `g`). Consulting only the first
				// meant a binding on an abstract subject was never compared,
				// even when its declaration already contradicted it.
				let actual = self
					.ctx
					.materialize_assoc_value(
						subject.ty,
						trait_bound.trait_index,
						binding.name.inner,
					)
					.or_else(|| {
						self.ctx.items.declared_assoc_value(
							self.ctx.types,
							subject.ty,
							trait_bound.trait_index,
							binding.name.inner,
						)
					});
				match &binding.rhs.inner {
					AssocBindingKind::Equals(rhs) => {
						if *rhs == TypeIndex::ERROR {
							continue;
						}
						// The RHS is written in the *declaring* item's scope,
						// so it may name that item's own type parameters
						// (`fn f<T: Has where { Item = U }, U>`) or an
						// inherited one from the parent impl. `type_args`
						// carries what the site being checked pinned those to
						// — empty at a declaration site, where they stay
						// abstract on purpose.
						let expected =
							self.ctx.substitute_type(*rhs, site.type_args);
						// A bare `Self` that no substitution covered still
						// means something different here than where it was
						// written: resolve it to this trait's receiver.
						let expected = match self.ctx.types.resolve(expected) {
							Type::TypeParam {
								owner: TypeParamOwner::Trait(_),
								param_index: 0,
							} => enclosing_self,
							_ => expected,
						};

						// The written value must satisfy the associated type's
						// own declared bounds (`type Assoc: Bound` on the
						// trait). One level: an impl's own conformance already
						// verified its associated types' deeper obligations.
						self.check_declared_bounds(
							site,
							trait_bound.trait_index,
							binding.name.inner,
							Subject::new(
								SourceSpan::new(
									binding.file_id,
									binding.rhs.span,
								),
								expected,
							),
							subject.ty,
							out,
						);

						// When the subject has a concrete impl, its real value
						// for this associated type has to equal what was
						// written. An `expected` that is *still* abstract
						// after substitution names a slot the site failed to
						// pin down (a phantom type param, already reported as
						// un-inferrable) — nothing to disprove, and comparing
						// it would stack a bogus mismatch on top of that.
						if let Some(actual) = actual
							&& actual != TypeIndex::ERROR
							&& expected != TypeIndex::ERROR
							&& !matches!(
								self.ctx.types.resolve(expected),
								Type::TypeParam { .. }
									| Type::AssocTypeProjection { .. }
									| Type::Infer
							) && expected != actual
						{
							out.push(self.report_equals_mismatch(
								site,
								subject,
								trait_bound,
								binding,
								(expected, actual),
							));
						}
					}
					AssocBindingKind::Bound(inner) => {
						// Recurse into the nested *trait* bounds — bounded by
						// how deep the `where` clause is literally written.
						// Against the subject's concrete associated value if it
						// has one, otherwise the abstract projection (which
						// `type_implements_trait` resolves through the
						// associated type's declared bounds).
						if !inner.traits.is_empty() {
							let value = actual.unwrap_or_else(|| {
								self.ctx.types.intern(
									Type::AssocTypeProjection {
										base: subject.ty,
										trait_index: trait_bound.trait_index,
										assoc_name: binding.name.inner,
									},
								)
							});
							// Keeps the subject's *place* while changing its
							// type: a nested level is still about the code the
							// caller wrote, and which nested constraint failed
							// is what the "required by a bound in" secondary
							// label already points at — in the file that
							// actually contains it.
							self.check_inner(
								site,
								subject.with_type(value),
								&inner.traits,
								subject.ty,
								out,
							);
						}
					}
				}
			}
		}
	}

	/// Check `value` against the bounds the trait declares for its associated
	/// type `at_trait::at_name` (`type at_name: Bound where { .. }`).
	///
	/// This follows the declaration edge — opening another declaration's
	/// bounds — exactly **once**, here. Everything below is written syntax and
	/// is walked by [`Self::check_written_bounds`], which cannot open a
	/// declaration at all. That split is what makes the whole thing terminate
	/// without a cycle guard: mutually-referential declarations
	/// (`type X: B where { Y = Self }` / `type Y: A where { X = Self }`) can
	/// only ping-pong if each hop is free to open the next declaration, and
	/// it isn't.
	///
	/// Not following the edge again is also *correct*, not just convenient: a
	/// value written inside a declared bound is in trait scope, so whether it
	/// satisfies its own associated type's declaration is a property of that
	/// declaration, which `validate_declarations` checks where it is written.
	fn check_declared_bounds(
		&mut self,
		site: BoundSite<'_>,
		at_trait: TraitIndex,
		at_name: SymbolU32,
		value: Subject,
		self_ty: TypeIndex,
		out: &mut Vec<Diagnostic<FileId>>,
	) {
		if value.ty == TypeIndex::ERROR {
			return;
		}
		// Copy the shared `&'a ItemRegistry` out of the field before looking
		// up: the result is then `&'a Bounds`, borrowed from the registry
		// rather than from `self`, so it survives the `&mut self` calls below
		// without a clone.
		let items: &'a ItemRegistry = self.ctx.items;
		let Some(bounds) = items
			.trait_associated_type(at_trait, at_name)
			.map(|assoc| &assoc.bounds)
		else {
			return;
		};
		// Re-attributed: these bounds were written on the trait's own
		// declaration, not at the site being checked.
		let site = site.attributed_to(BoundOrigin::TraitAssocType {
			trait_index: at_trait,
			name: at_name,
		});
		self.check_written_bounds(site, value, bounds, self_ty, out);
	}

	/// Check `value` against a written bound tree: trait membership, then each
	/// refinement's own bindings, all the way down the nesting as written.
	///
	/// Terminates by construction — every recursive call takes a strict
	/// subterm of `required`, and nothing here opens a declaration's bounds,
	/// so there is no declaration-to-declaration edge to cycle on. See
	/// [`Self::check_declared_bounds`], which follows that edge once before
	/// handing over.
	///
	/// `self_ty` binds `Self` throughout, unchanged by the descent: the whole
	/// tree was written in one scope, so `Self` means the same thing at every
	/// level of it.
	fn check_written_bounds(
		&mut self,
		site: BoundSite<'_>,
		value: Subject,
		required: &Bounds,
		self_ty: TypeIndex,
		out: &mut Vec<Diagnostic<FileId>>,
	) {
		for declared in required.traits.iter() {
			if !self.ctx.items.type_implements_trait(
				self.ctx.types,
				value.ty,
				declared.trait_index,
			) {
				out.push(self.report_missing_trait(site, value, declared));
				continue;
			}
			// Only a concrete impl exposes actual associated values to check
			// this bound's own `where` refinements against.
			for refinement in declared.bindings.iter() {
				let Some(actual) = self.ctx.materialize_assoc_value(
					value.ty,
					declared.trait_index,
					refinement.name.inner,
				) else {
					continue;
				};
				if actual == TypeIndex::ERROR {
					continue;
				}
				match &refinement.rhs.inner {
					AssocBindingKind::Equals(sub_rhs) => {
						// A written RHS here is in trait scope: the only type
						// parameter it can name is that trait's `Self`, so
						// full substitution is safe.
						let expected =
							self.ctx.substitute_type(*sub_rhs, &[self_ty]);
						if expected != TypeIndex::ERROR && expected != actual {
							out.push(self.report_equals_mismatch(
								site,
								value,
								declared,
								refinement,
								(expected, actual),
							));
						}
					}
					// The nested level, against this refinement's own concrete
					// value. Checking only `sub_req`'s trait membership and
					// stopping — as this used to — silently dropped every
					// obligation written inside it.
					AssocBindingKind::Bound(sub_req) => self
						.check_written_bounds(
							site,
							value.with_type(actual),
							sub_req,
							self_ty,
							out,
						),
				}
			}
		}
	}

	/// The concrete `Self` for `origin`'s own `where` clause — an impl's
	/// target, a trait's `Self` parameter, or `None` for a context that has
	/// no `Self` (a free function, a struct). Deeper frames' `Self` is
	/// supplied by the recursion itself (the parent subject).
	fn origin_self_ty(&mut self, origin: BoundOrigin) -> Option<TypeIndex> {
		let owner = match origin {
			BoundOrigin::TypeParam { owner, .. } => owner,
			BoundOrigin::TraitAssocType { trait_index, .. } => {
				return Some(self.trait_self_type(trait_index));
			}
		};
		match owner {
			TypeParamOwner::Trait(trait_index) => {
				Some(self.trait_self_type(trait_index))
			}
			TypeParamOwner::InherentImpl(index) => Some(
				self.ctx.items.inherent_impls[usize::from(index)]
					.target
					.inner,
			),
			TypeParamOwner::TraitImpl(index) => Some(
				self.ctx.items.trait_impls[usize::from(index)].target.inner,
			),
			TypeParamOwner::Function(def_id) => {
				let func_index = self.ctx.items.function_index(def_id)?;
				let parent = self.ctx.items.functions[usize::from(func_index)]
					.type_param_parent()?;
				self.origin_self_ty(BoundOrigin::TypeParam {
					owner: parent,
					index: 0,
				})
			}
			TypeParamOwner::Struct(_) | TypeParamOwner::TypeAlias(_) => None,
		}
	}

	fn trait_self_type(&mut self, trait_index: TraitIndex) -> TypeIndex {
		self.ctx.types.intern(Type::TypeParam {
			owner: TypeParamOwner::Trait(trait_index),
			param_index: 0,
		})
	}

	fn formatter(&self, namespace: NamespaceIndex) -> TypeFormatter<'_> {
		TypeFormatter::new(
			&*self.ctx.types,
			self.ctx.items,
			self.modules,
			self.ctx.interner,
			self.packages,
			self.modules.namespaces[usize::from(namespace)].package,
		)
	}

	/// `(file, "name")` for the "required by a bound in `name`" secondary
	/// label. A trait impl has no name of its own, so its target type stands
	/// in.
	fn origin_label(&self, origin: BoundOrigin) -> (FileId, String) {
		match origin {
			BoundOrigin::TraitAssocType { trait_index, name } => {
				let trait_ = &self.ctx.items.traits[usize::from(trait_index)];
				let trait_name =
					self.ctx.interner.resolve(trait_.name.inner).unwrap();
				let assoc_name = self.ctx.interner.resolve(name).unwrap();
				(trait_.file_id, format!("{trait_name}::{assoc_name}"))
			}
			BoundOrigin::TypeParam {
				owner: TypeParamOwner::Trait(trait_index),
				..
			} => {
				let trait_ = &self.ctx.items.traits[usize::from(trait_index)];
				(
					trait_.file_id,
					self.ctx
						.interner
						.resolve(trait_.name.inner)
						.unwrap()
						.to_string(),
				)
			}
			BoundOrigin::TypeParam {
				owner: TypeParamOwner::InherentImpl(index),
				..
			} => {
				let imp = &self.ctx.items.inherent_impls[usize::from(index)];
				(
					imp.file_id,
					self.formatter(imp.namespace)
						.display_type(imp.target.inner)
						.unwrap_or_default(),
				)
			}
			BoundOrigin::TypeParam {
				owner: TypeParamOwner::TraitImpl(index),
				..
			} => {
				let imp = &self.ctx.items.trait_impls[usize::from(index)];
				(
					imp.file_id,
					self.formatter(imp.namespace)
						.display_type(imp.target.inner)
						.unwrap_or_default(),
				)
			}
			BoundOrigin::TypeParam {
				owner:
					TypeParamOwner::Function(def_id)
					| TypeParamOwner::Struct(def_id)
					| TypeParamOwner::TypeAlias(def_id),
				..
			} => {
				let (name, span) = self
					.ctx
					.items
					.item_name(def_id)
					.expect("bound origin item must be named");
				(
					span.file_id,
					self.ctx.interner.resolve(name).unwrap().to_string(),
				)
			}
		}
	}

	fn report_missing_trait(
		&self,
		site: BoundSite<'_>,
		subject: Subject,
		trait_bound: &TraitBound,
	) -> Diagnostic<FileId> {
		let subject_name = self
			.formatter(site.namespace)
			.display_type(subject.ty)
			.unwrap_or_default();
		let trait_name = self
			.ctx
			.interner
			.resolve(
				self.ctx.items.traits[usize::from(trait_bound.trait_index)]
					.name
					.inner,
			)
			.unwrap()
			.to_string();
		let (origin_file, origin_name) = self.origin_label(site.origin);
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the trait bound `{subject_name}: {trait_name}` is not satisfied"
			))
			.with_label(subject.at.primary_label().with_message(format!(
				"the trait `{trait_name}` is not implemented for `{subject_name}`"
			)))
			.with_label(
				Label::secondary(origin_file, trait_bound.span).with_message(
					format!("required by a bound in `{origin_name}`"),
				),
			)
	}

	fn report_equals_mismatch(
		&self,
		site: BoundSite<'_>,
		subject: Subject,
		trait_bound: &TraitBound,
		binding: &AssocBinding,
		mismatch: (TypeIndex, TypeIndex),
	) -> Diagnostic<FileId> {
		let (expected, actual) = mismatch;
		let formatter = self.formatter(site.namespace);
		let subject_name =
			formatter.display_type(subject.ty).unwrap_or_default();
		let expected_name =
			formatter.display_type(expected).unwrap_or_default();
		let actual_name = formatter.display_type(actual).unwrap_or_default();
		let assoc_name = self
			.ctx
			.interner
			.resolve(binding.name.inner)
			.unwrap()
			.to_string();
		let (origin_file, origin_name) = self.origin_label(site.origin);
		// Not "the trait bound `T: Trait` is not satisfied": the trait *is*
		// implemented — `check_inner` reports and skips when it isn't — and
		// only the binding disagrees. `trait_bound` is still what carries the
		// span of the obligation, so it names the secondary label.
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitBoundViolation.code())
			.with_message(format!(
				"the associated type binding `{assoc_name} = {expected_name}` is not satisfied"
			))
			.with_label(
				subject
					.at
					.primary_label()
					.with_message(format!(
						"`{subject_name}::{assoc_name}` is `{actual_name}`, not `{expected_name}`"
					)),
			)
			.with_label(
				Label::secondary(origin_file, trait_bound.span).with_message(
					format!("required by a bound in `{origin_name}`"),
				),
			)
	}
}
