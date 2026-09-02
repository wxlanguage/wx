//! Read-only structural comparison between a trait item's declared type and
//! the corresponding impl item's — the E0053-style "incompatible signature"
//! check `check_trait_conformance` defers to.
//!
//! The core problem this exists to avoid: `substitute_type` (generics.rs)
//! materializes a concrete instantiation as a byproduct of resolving a type,
//! which is right for the signature phase (the result is stored in TIR) but
//! wrong for conformance checking, which only ever needs a yes/no answer plus
//! a diagnostic — it shouldn't grow the type pool to get one. `compare_types`
//! never calls `intern_type`: instead of substituting `Self`/an impl's own
//! generics into a *new* type and comparing the result, it walks the trait
//! side's original type tree and the impl side's original type tree in
//! lockstep, resolving an abstract node to whatever it means *right here*
//! only when the walk actually reaches it.
//!
//! `Frame` is what makes that possible without re-deriving the general
//! `TypeView`/`Substitution` machinery this module replaced: it's a small,
//! borrowed, single-purpose chain (never `Rc`, never cloned, never outlives
//! one comparison call) recording only the two things this comparison can
//! ever need to know about an abstract node — the trait's own `Self`
//! (`Frame::Root`, always present, always the base of the chain — a trait
//! has exactly one type param, so there's nothing else `Self` could mean),
//! and, once a projection has been resolved through `find_trait_impl`, that
//! one impl's own inferred type arguments (`Frame::Bind`). Each `Frame::Bind`
//! is scoped to exactly the `find_trait_impl` call that produced it and
//! discarded the moment that subtree's comparison returns — there is
//! deliberately no general owner-keyed environment here, because nothing in
//! this comparison ever needs one: a method's own generics are matched by
//! relative position against the *other* function's own generics (read
//! straight off `Function::inherited_type_param_count`, never threaded in as
//! context), and an associated-type projection's impl-side arguments are
//! always self-contained to the one impl that produced them, never nested
//! onto an unrelated outer scope.

use super::*;

/// A type as interpreted "here" — `index` on its own, plus whatever
/// substitution frame is active at this point in the walk. The impl side of
/// a comparison never actually needs a non-trivial frame today (an impl's
/// own signature is always compared symbolically, never substituted — see
/// `compare_unresolved_type_param`); it's wrapped in `TypeRef` the same way
/// as the trait side purely for symmetry in `compare_types`'s signature, not
/// because the two frames are ever compared against each other — see the
/// note on `compare_types`'s fast path for why frame *identity* is
/// deliberately not part of equality here.
#[derive(Clone, Copy)]
struct TypeRef<'f> {
	index: TypeIndex,
	frame: &'f Frame<'f>,
}

enum Frame<'f> {
	Root {
		self_ty: TypeIndex,
	},
	Bind {
		owner: TypeParamOwner,
		args: &'f [TypeIndex],
		/// The frame that was active when `args` was derived — resolving
		/// something inside `args[i]` that isn't *this* impl's own param
		/// falls through to here, not back into `self`.
		parent: &'f Frame<'f>,
	},
}

impl<'f> Frame<'f> {
	fn resolve(
		&'f self,
		owner: TypeParamOwner,
		index: u32,
	) -> Option<TypeRef<'f>> {
		match self {
			Frame::Root { self_ty }
				if matches!(owner, TypeParamOwner::Trait(_)) =>
			{
				Some(TypeRef {
					index: *self_ty,
					frame: self,
				})
			}
			Frame::Bind {
				owner: bound_owner,
				args,
				parent,
			} if *bound_owner == owner => Some(TypeRef {
				index: args[index as usize],
				frame: parent,
			}),
			Frame::Bind { parent, .. } => parent.resolve(owner, index),
			_ => None,
		}
	}
}

/// A queue of associated-type projections still waiting to be applied to
/// some base, most-recently-queued first. Exists because a projection's
/// base can itself be an unresolved projection (`Self::Mid::Out` — the
/// base of the outer `::Out` is `Self::Mid`, itself a projection):
/// discovering that mid-resolution means "go resolve the inner one first,
/// then come back and apply the outer one" — `Pending` is that "come back
/// and apply" queue.
///
/// Borrowed and singly-linked the exact same way `Frame` is, and for the
/// same reason: each node is built locally (in `resolve_and_compare`) and
/// passed straight into a nested recursive call, never returned — so it
/// never needs to outlive the call that built it, and needs no allocation.
/// Representing "what's still left to do" as data instead of a closure is
/// what keeps this plain recursive function calls, with no dynamic
/// dispatch anywhere.
enum Pending<'p> {
	Done,
	Step {
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
		rest: &'p Pending<'p>,
	},
}

fn classify_difference(expected: &Type, found: &Type) -> TypeDifferenceKind {
	match (expected, found) {
		(
			Type::Struct {
				struct_index: a, ..
			},
			Type::Struct {
				struct_index: b, ..
			},
		) if a != b => TypeDifferenceKind::Nominal,
		(Type::Struct { args: a, .. }, Type::Struct { args: b, .. })
			if a.len() != b.len() =>
		{
			TypeDifferenceKind::TypeArgumentCount
		}
		(Type::Enum { enum_index: a }, Type::Enum { enum_index: b })
			if a != b =>
		{
			TypeDifferenceKind::Nominal
		}
		(
			Type::Pointer { ownership: a, .. },
			Type::Pointer { ownership: b, .. },
		)
		| (
			Type::Array { ownership: a, .. },
			Type::Array { ownership: b, .. },
		)
		| (
			Type::Slice { ownership: a, .. },
			Type::Slice { ownership: b, .. },
		) if a != b => TypeDifferenceKind::Ownership,
		(Type::Array { size: a, .. }, Type::Array { size: b, .. })
			if a != b =>
		{
			TypeDifferenceKind::ArrayLength
		}
		(Type::Tuple { elements: a }, Type::Tuple { elements: b })
			if a.len() != b.len() =>
		{
			TypeDifferenceKind::TupleLength
		}
		(
			Type::FunctionItem { id: a, .. },
			Type::FunctionItem { id: b, .. },
		) if a != b => TypeDifferenceKind::Nominal,
		_ => TypeDifferenceKind::Shape,
	}
}

/// Where the first meaningful difference occurred, and what kind it was.
#[derive(Clone)]
pub(super) struct TypeDifference {
	pub(super) path: Vec<TypePathElement>,
	/// Always a real, already-interned leaf — `compare_types` only reaches
	/// the point of reporting a `Different` once neither side is a
	/// `TypeParam`/`AssocTypeProjection` any more (peeling happens eagerly,
	/// at every node, before comparison), so nothing half-resolved or
	/// frame-dependent is ever stored here.
	pub(super) expected: TypeIndex,
	pub(super) found: TypeIndex,
	pub(super) kind: TypeDifferenceKind,
}

#[derive(Clone, Copy)]
pub(super) enum TypePathElement {
	TupleElement(usize),
	TypeArgument(usize),
	FunctionParameter(usize),
	FunctionResult,
	Pointee,
	ArrayElement,
	SliceElement,
	Memory,
}

#[derive(Clone, Copy)]
pub(super) enum TypeDifferenceKind {
	Shape,
	Nominal,
	Ownership,
	ArrayLength,
	TupleLength,
	ParameterCount,
	TypeArgumentCount,
	TypeParam,
}

pub(super) enum TypeComparison {
	Equivalent,
	Different(TypeDifference),
	/// Comparison could not produce a meaningful answer — an earlier type
	/// error, a missing associated-type implementation, or a receiver that
	/// couldn't be resolved far enough to look anything up. Always treated
	/// as "couldn't prove," never promoted to `Different`, so it doesn't
	/// cascade a second, misleading diagnostic on top of whatever already
	/// explains the missing information. No reason payload: nothing
	/// downstream distinguishes *why* yet (every case is silence, the same
	/// way an `Error`/`Infer` type already means "some other diagnostic
	/// covers this") — add one back if a future caller (e.g. `check_assoc_
	/// type_bounds`, once it's rewritten onto this same comparator) needs
	/// to react differently per reason.
	Indeterminate,
}

pub(super) enum SignatureComparison {
	Compatible,
	Incompatible(SignatureDifference),
	Indeterminate,
}

pub(super) enum SignatureDifference {
	TypeParameterCount {
		expected: usize,
		found: usize,
	},
	ParameterCount {
		expected: usize,
		found: usize,
	},
	Parameter {
		index: usize,
		difference: TypeDifference,
	},
	ReturnType {
		difference: TypeDifference,
	},
	// Bound compatibility (an impl method must not require stricter bounds
	// than the trait method declares) is a separate obligation-proving
	// concern from type equivalence, and isn't implemented yet — no variant
	// here for it until it is, rather than a placeholder nothing produces.
}

impl<'ast> Builder<'ast, '_> {
	/// Compares a trait method's declared signature against the
	/// corresponding impl method's, entirely without touching
	/// `self.types`/`self.items` mutably.
	pub(super) fn compare_method_signature(
		&self,
		trait_fn_index: FunctionIndex,
		impl_fn_index: FunctionIndex,
		trait_impl: &TraitImpl,
	) -> SignatureComparison {
		let trait_fn = &self.items.functions[usize::from(trait_fn_index)];
		let impl_fn = &self.items.functions[usize::from(impl_fn_index)];

		if trait_fn.type_params.len() != impl_fn.type_params.len() {
			return SignatureComparison::Incompatible(
				SignatureDifference::TypeParameterCount {
					expected: trait_fn.type_params.len(),
					found: impl_fn.type_params.len(),
				},
			);
		}
		if trait_fn.params.len() != impl_fn.params.len() {
			return SignatureComparison::Incompatible(
				SignatureDifference::ParameterCount {
					expected: trait_fn.params.len(),
					found: impl_fn.params.len(),
				},
			);
		}

		let root = Frame::Root {
			self_ty: trait_impl.target.inner,
		};
		// Reused across every parameter and the return type below, rather
		// than a fresh `Vec::new()` per comparison: `path` is always back
		// to empty by the time `compare_types` returns (the `recurse!`
		// macro's `pop` is unconditional, running before the `match result
		// { other => return other }` that might propagate a failure), so
		// there's nothing to reset beyond a debug-only sanity check.
		let mut path = Vec::new();
		for (index, (expected, found)) in trait_fn
			.params
			.iter()
			.zip(impl_fn.params.iter())
			.enumerate()
		{
			debug_assert!(path.is_empty());
			match self.compare_types(
				TypeRef {
					index: expected.ty.inner,
					frame: &root,
				},
				TypeRef {
					index: found.ty.inner,
					frame: &root,
				},
				&mut path,
			) {
				TypeComparison::Equivalent => {}
				TypeComparison::Different(difference) => {
					return SignatureComparison::Incompatible(
						SignatureDifference::Parameter { index, difference },
					);
				}
				TypeComparison::Indeterminate => {
					return SignatureComparison::Indeterminate;
				}
			}
		}

		let expected_result =
			trait_fn.result.map_or(TypeIndex::UNIT, |r| r.inner);
		let found_result = impl_fn.result.map_or(TypeIndex::UNIT, |r| r.inner);
		debug_assert!(path.is_empty());
		match self.compare_types(
			TypeRef {
				index: expected_result,
				frame: &root,
			},
			TypeRef {
				index: found_result,
				frame: &root,
			},
			&mut path,
		) {
			TypeComparison::Equivalent => SignatureComparison::Compatible,
			TypeComparison::Different(difference) => {
				SignatureComparison::Incompatible(
					SignatureDifference::ReturnType { difference },
				)
			}
			TypeComparison::Indeterminate => SignatureComparison::Indeterminate,
		}
	}

	pub(super) fn compare_assoc_const_type(
		&self,
		trait_const_index: ConstIndex,
		impl_const_index: ConstIndex,
		trait_impl: &TraitImpl,
	) -> TypeComparison {
		let trait_const = &self.items.constants[usize::from(trait_const_index)];
		let impl_const = &self.items.constants[usize::from(impl_const_index)];
		let root = Frame::Root {
			self_ty: trait_impl.target.inner,
		};
		self.compare_types(
			TypeRef {
				index: trait_const.ty.inner,
				frame: &root,
			},
			TypeRef {
				index: impl_const.ty.inner,
				frame: &root,
			},
			&mut Vec::new(),
		)
	}

	fn compare_types(
		&self,
		expected: TypeRef<'_>,
		found: TypeRef<'_>,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		let expected_ty = self.types.resolve(expected.index);
		let found_ty = self.types.resolve(found.index);
		if matches!(expected_ty, Type::Error | Type::Infer)
			|| matches!(found_ty, Type::Error | Type::Infer)
		{
			return TypeComparison::Indeterminate;
		}
		// Frame identity is deliberately not part of this check — only the
		// raw `TypeIndex` is compared. Safe here specifically because of
		// this comparator's narrow scope, not as a general property of
		// `TypeRef`: every top-level call (`compare_method_signature`/
		// `compare_assoc_const_type`) is scoped to one trait item vs. one
		// impl item, for one `TraitImpl`, so `expected` and `found` always
		// trace back to the *same* `Frame::Root`. Any `Frame::Bind` built
		// along the way (via `find_trait_impl`, resolving a projection) is
		// derived from that same root — so if resolution ever reaches the
		// *same* impl again (e.g. checking `impl<X: Container> Container
		// for Wrap<X> { type Elem = X; }`'s own conformance, where
		// `Self::Elem` unifies `Wrap<X>` against its own target), the args
		// bound to it are necessarily an identity mapping: unifying an
		// impl's own pattern against its own target always binds each
		// parameter to itself. So two operands can only collide on the
		// same raw `TypeIndex` when they denote the literal same
		// declaration — in which case they mean the same thing no matter
		// which frame object happens to be attached to each. `found`
		// specifically never even routes through a `Frame::Bind` at all
		// (see `reduce_found`), so in practice this only has to hold for
		// `expected`.
		if expected.index == found.index {
			return TypeComparison::Equivalent;
		}

		// Same-shape alpha-equivalence, checked before any resolution is
		// attempted: `T::Item` vs `U::Item`, where `T`/`U` are
		// corresponding method generics, compares equal via a recursive
		// call on the bases (which bottoms out in
		// `compare_unresolved_type_param`) — no `find_trait_impl` lookup
		// needed, and this has to run first because `T`/`U` alone usually
		// aren't dispatchable at all (a bare method-owned type param isn't
		// a valid `find_trait_impl` receiver).
		if let (
			&Type::AssocTypeProjection {
				base: eb,
				trait_index: et,
				assoc_name: ea,
			},
			&Type::AssocTypeProjection {
				base: fb,
				trait_index: ft,
				assoc_name: fa,
			},
		) = (expected_ty, found_ty)
			&& et == ft
			&& ea == fa
			&& let TypeComparison::Equivalent = self.compare_types(
				TypeRef {
					index: eb,
					frame: expected.frame,
				},
				TypeRef {
					index: fb,
					frame: found.frame,
				},
				path,
			) {
			return TypeComparison::Equivalent;
		}

		self.resolve_and_compare(expected, &Pending::Done, found, path)
	}

	/// Resolves `expected` — peeling a bare `TypeParam` through its frame,
	/// and queueing an `AssocTypeProjection` head onto `pending` before
	/// diving into its own base — until it's something neither of those,
	/// then hands off to [`Self::apply_pending`]. This is what lets a chain
	/// like `Self::Mid::Out` unwind one link at a time: `Out` gets queued
	/// while resolving `Self::Mid`, which itself queues `Mid` while
	/// resolving `Self`, which peels straight to a concrete type via
	/// `Frame::Root` — at which point `apply_pending` starts working the
	/// queue back off, `Mid` first, then `Out`.
	fn resolve_and_compare(
		&self,
		expected: TypeRef<'_>,
		pending: &Pending<'_>,
		found: TypeRef<'_>,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		match self.types.resolve(expected.index) {
			Type::TypeParam { owner, param_index } => {
				match expected.frame.resolve(*owner, *param_index) {
					Some(next) => {
						self.resolve_and_compare(next, pending, found, path)
					}
					// Method-owned — stays abstract, no frame will ever
					// resolve it further.
					None => self.apply_pending(expected, pending, found, path),
				}
			}
			&Type::AssocTypeProjection {
				base,
				trait_index,
				assoc_name,
			} => {
				let deeper = Pending::Step {
					trait_index,
					assoc_name,
					rest: pending,
				};
				self.resolve_and_compare(
					TypeRef {
						index: base,
						frame: expected.frame,
					},
					&deeper,
					found,
					path,
				)
			}
			_ => self.apply_pending(expected, pending, found, path),
		}
	}

	/// `expected` is confirmed to be neither a `TypeParam` nor an
	/// `AssocTypeProjection` itself (that's what every call site already
	/// established before reaching here). If `pending` has a queued step,
	/// apply it — via a declared equality binding on `expected`'s own
	/// bounds first (`T: Container where { Item = i32 }` proves the
	/// projection without a concrete impl for `T`), else the existing
	/// `find_trait_impl` — and resolve whatever that produces the same way
	/// (it may itself be a `TypeParam`/projection, e.g. `impl<X: Container>
	/// Container for Wrap<X> { type Elem = X::Elem; }`). Once `pending` is
	/// exhausted, `expected` is the final answer: compare it against
	/// `found` for real.
	fn apply_pending(
		&self,
		expected: TypeRef<'_>,
		pending: &Pending<'_>,
		found: TypeRef<'_>,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		let &Pending::Step {
			trait_index,
			assoc_name,
			rest,
		} = pending
		else {
			return self.compare_resolved(expected, found, path);
		};

		if let Some(bound_value) =
			self.resolve_projection_via_bound(expected, trait_index, assoc_name)
		{
			return self.resolve_and_compare(
				TypeRef {
					index: bound_value,
					frame: expected.frame,
				},
				rest,
				found,
				path,
			);
		}

		match self.items.find_trait_impl(
			&self.types,
			expected.index,
			trait_index,
		) {
			Some((impl_index, impl_args)) => {
				let Some(raw) =
					self.assoc_type_raw_value(impl_index, assoc_name)
				else {
					return TypeComparison::Indeterminate;
				};
				let next_frame = Frame::Bind {
					owner: TypeParamOwner::TraitImpl(impl_index),
					args: &impl_args,
					parent: expected.frame,
				};
				self.resolve_and_compare(
					TypeRef {
						index: raw,
						frame: &next_frame,
					},
					rest,
					found,
					path,
				)
			}
			// Never promoted to `Different`: either genuinely no impl, or
			// `expected` was still partially abstract in a way
			// `infer_type_args` can't unify (e.g. a repeated impl type
			// param occurring at two positions bound to two different-but-
			// equal frame values — its repeated-binding check compares raw
			// indexes). Both cases mean "couldn't prove," not "proved
			// false."
			None => TypeComparison::Indeterminate,
		}
	}

	/// `expected` is fully resolved — no more `Pending` steps, and (per
	/// `resolve_and_compare`'s own dispatch) not a `TypeParam` with
	/// anything further its frame could do for it. Only two things left it
	/// could still be: a method-owned type param needing alpha-equivalence
	/// against `found`, or something concrete needing a real structural
	/// comparison.
	///
	/// `found` gets one more chance to reduce here, via
	/// [`Self::reduce_found`], rather than up front alongside `expected` —
	/// reducing it earlier would risk short-circuiting `compare_types`'s
	/// same-shape alpha-equivalence check (`T::Item` vs `U::Item`) on cases
	/// where that check, not a bound reduction, is the right way to prove
	/// equivalence. This is purely a fallback for when structural
	/// comparison is about to fail anyway.
	fn compare_resolved(
		&self,
		expected: TypeRef<'_>,
		found: TypeRef<'_>,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		// Same safety argument as `compare_types`'s own fast path — see
		// there. `expected` may have changed since that check ran (this is
		// reached after `resolve_and_compare`/`apply_pending` resolve it
		// further), so it's re-checked here rather than assumed.
		if expected.index == found.index {
			return TypeComparison::Equivalent;
		}
		match self.types.resolve(expected.index) {
			Type::TypeParam { owner, param_index } => self
				.compare_unresolved_type_param(
					expected,
					*owner,
					*param_index,
					found,
					path,
				),
			_ => {
				let reduced_found = self.reduce_found(found);
				if reduced_found.index != found.index {
					self.compare_types(expected, reduced_found, path)
				} else {
					self.compare_structural(expected, found, path)
				}
			}
		}
	}

	/// Resolves `found` — the impl side of a comparison — as far as
	/// declared equality bindings alone can take it. Never
	/// `find_trait_impl`, never a new `Frame`: an impl's own signature
	/// can't reduce any other way. Anything `find_trait_impl` could have
	/// resolved was already flattened during Phase 2 signature building
	/// (see `resolve_namespace_type_member`'s eager catch-all for a
	/// concrete/composite base) — what can still be unresolved here is
	/// exactly a projection whose base is one of the impl's *own*
	/// still-abstract generics, which never gets bound to a concrete value
	/// during signature comparison (there's no receiver; we're comparing
	/// declarations, not instantiating anything). The only way such a
	/// projection can mean something concrete is a `where { Name = T }`
	/// binding its own base declared — e.g. `V: Inner where { Out = i32 }`
	/// is what lets `V::Out` reduce to `i32`.
	///
	/// Since nothing here ever constructs a new `Frame`, this can just
	/// return a `TypeRef` by value — unlike resolving `expected`, there's
	/// no lifetime problem to route around with `Pending`/recursion into a
	/// continuation.
	fn reduce_found<'f>(&self, found: TypeRef<'f>) -> TypeRef<'f> {
		let &Type::AssocTypeProjection {
			base,
			trait_index,
			assoc_name,
		} = self.types.resolve(found.index)
		else {
			return found;
		};
		let base_ref = TypeRef {
			index: base,
			frame: found.frame,
		};
		match self.resolve_projection_via_bound(
			base_ref,
			trait_index,
			assoc_name,
		) {
			Some(resolved) => self.reduce_found(TypeRef {
				index: resolved,
				frame: found.frame,
			}),
			None => found,
		}
	}

	/// `expected` is a `TypeParam` whose owner isn't resolvable via `frame`
	/// — the only way that happens is a method's own generic (Self is
	/// always resolvable via `Frame::Root`, and an impl's own `TraitImpl`
	/// params only ever appear already bound inside a `Frame::Bind`). Only
	/// equivalent to a `found` that is the *impl* method's own generic, at
	/// the same relative position — read directly from each function's own
	/// `inherited_type_param_count`, never threaded in as context. A
	/// function's signature can only ever reference its own generic scope
	/// (or its parent's inherited one) — see `resolve_type_identifier`'s
	/// scoping — so the two owners seen here can only ever be this trait
	/// method's own id and this impl method's own id; nothing else could
	/// have contributed a Function-owned param to either side.
	fn compare_unresolved_type_param(
		&self,
		expected: TypeRef<'_>,
		expected_owner: TypeParamOwner,
		expected_index: u32,
		found: TypeRef<'_>,
		path: &[TypePathElement],
	) -> TypeComparison {
		let mismatch = || {
			TypeComparison::Different(TypeDifference {
				path: path.to_vec(),
				expected: expected.index,
				found: found.index,
				kind: TypeDifferenceKind::TypeParam,
			})
		};
		let (
			TypeParamOwner::Function(expected_fn),
			&Type::TypeParam {
				owner: TypeParamOwner::Function(found_fn),
				param_index: found_index,
			},
		) = (expected_owner, self.types.resolve(found.index))
		else {
			return mismatch();
		};
		let expected_offset = self.items.functions
			[usize::from(self.items.expect_function_index(expected_fn))]
		.inherited_type_param_count as u32;
		let found_offset = self.items.functions
			[usize::from(self.items.expect_function_index(found_fn))]
		.inherited_type_param_count as u32;
		if expected_index - expected_offset == found_index - found_offset {
			TypeComparison::Equivalent
		} else {
			mismatch()
		}
	}

	/// `base`'s own declared bounds (via the existing, already read-only
	/// `ItemRegistry::abstract_type_bounds`) for a `where { assoc_name =
	/// T }`-style equality binding on `trait_index`. This is what lets
	/// `T::Item` compare equal to `i32` when `T: Container where { Item =
	/// i32 }`, without ever finding a concrete impl for `T` — the same
	/// "prove from assumptions" step `check_assoc_type_bounds` will need for
	/// its own false-positive gap (see the `T::Elem: Bound` ignored test).
	fn resolve_projection_via_bound(
		&self,
		base: TypeRef<'_>,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Option<TypeIndex> {
		let bounds =
			self.items.abstract_type_bounds(&self.types, base.index)?;
		let trait_bound = bounds
			.traits
			.iter()
			.find(|bound| bound.trait_index == trait_index)?;
		trait_bound
			.bindings
			.iter()
			.find_map(|(name, kind)| match kind {
				AssocBindingKind::Equals(ty) if *name == assoc_name => {
					Some(*ty)
				}
				_ => None,
			})
	}

	fn assoc_type_raw_value(
		&self,
		impl_index: TraitImplIndex,
		assoc_name: SymbolU32,
	) -> Option<TypeIndex> {
		match self.items.trait_impls[usize::from(impl_index)]
			.members
			.get(&assoc_name)?
		{
			ImplEntry::AssocType(idx) => {
				Some(self.items.assoc_type_impls[usize::from(*idx)].ty?.inner)
			}
			_ => None,
		}
	}

	fn compare_structural(
		&self,
		expected: TypeRef<'_>,
		found: TypeRef<'_>,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		macro_rules! recurse {
			($element:expr, $e:expr, $f:expr) => {{
				path.push($element);
				let result = self.compare_types(
					TypeRef {
						index: $e,
						frame: expected.frame,
					},
					TypeRef {
						index: $f,
						frame: found.frame,
					},
					path,
				);
				path.pop();
				match result {
					TypeComparison::Equivalent => {}
					other => return other,
				}
			}};
		}

		match (
			self.types.resolve(expected.index),
			self.types.resolve(found.index),
		) {
			(Type::Tuple { elements: e }, Type::Tuple { elements: f }) => {
				if e.len() != f.len() {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::TupleLength,
					);
				}
				for (index, (&ei, &fi)) in e.iter().zip(f.iter()).enumerate() {
					recurse!(TypePathElement::TupleElement(index), ei, fi);
				}
				TypeComparison::Equivalent
			}
			(
				&Type::Pointer {
					to: et,
					memory: em,
					ownership: eown,
				},
				&Type::Pointer {
					to: ft,
					memory: fm,
					ownership: fown,
				},
			) => {
				if eown != fown {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::Ownership,
					);
				}
				recurse!(TypePathElement::Pointee, et, ft);
				recurse!(TypePathElement::Memory, em, fm);
				TypeComparison::Equivalent
			}
			(
				&Type::Array {
					of: e_of,
					size: es,
					memory: em,
					ownership: eown,
				},
				&Type::Array {
					of: f_of,
					size: fs,
					memory: fm,
					ownership: fown,
				},
			) => {
				if eown != fown {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::Ownership,
					);
				}
				if es != fs {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::ArrayLength,
					);
				}
				recurse!(TypePathElement::ArrayElement, e_of, f_of);
				recurse!(TypePathElement::Memory, em, fm);
				TypeComparison::Equivalent
			}
			(
				&Type::Slice {
					of: e_of,
					memory: em,
					ownership: eown,
				},
				&Type::Slice {
					of: f_of,
					memory: fm,
					ownership: fown,
				},
			) => {
				if eown != fown {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::Ownership,
					);
				}
				recurse!(TypePathElement::SliceElement, e_of, f_of);
				recurse!(TypePathElement::Memory, em, fm);
				TypeComparison::Equivalent
			}
			(
				Type::Struct {
					struct_index: esi,
					args: ea,
				},
				Type::Struct {
					struct_index: fsi,
					args: fa,
				},
			) => {
				if esi != fsi {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::Nominal,
					);
				}
				if ea.len() != fa.len() {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::TypeArgumentCount,
					);
				}
				for (index, (&ei, &fi)) in ea.iter().zip(fa.iter()).enumerate()
				{
					recurse!(TypePathElement::TypeArgument(index), ei, fi);
				}
				TypeComparison::Equivalent
			}
			(
				Type::Function { signature: es },
				Type::Function { signature: fs },
			) => {
				if es.params().len() != fs.params().len() {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::ParameterCount,
					);
				}
				let (eresult, fresult) = (es.result(), fs.result());
				for (index, (&ei, &fi)) in
					es.params().iter().zip(fs.params().iter()).enumerate()
				{
					recurse!(TypePathElement::FunctionParameter(index), ei, fi);
				}
				recurse!(TypePathElement::FunctionResult, eresult, fresult);
				TypeComparison::Equivalent
			}
			(
				&Type::FunctionItem {
					id: ei,
					type_args: ref ea,
				},
				&Type::FunctionItem {
					id: fi,
					type_args: ref fa,
				},
			) => {
				if ei != fi || ea.len() != fa.len() {
					return self.different(
						expected,
						found,
						path,
						TypeDifferenceKind::Nominal,
					);
				}
				for (index, (&ei, &fi)) in ea.iter().zip(fa.iter()).enumerate()
				{
					recurse!(TypePathElement::TypeArgument(index), ei, fi);
				}
				TypeComparison::Equivalent
			}
			(expected_ty, found_ty) => {
				let kind = classify_difference(expected_ty, found_ty);
				self.different(expected, found, path, kind)
			}
		}
	}

	fn different(
		&self,
		expected: TypeRef<'_>,
		found: TypeRef<'_>,
		path: &[TypePathElement],
		kind: TypeDifferenceKind,
	) -> TypeComparison {
		TypeComparison::Different(TypeDifference {
			path: path.to_vec(),
			expected: expected.index,
			found: found.index,
			kind,
		})
	}

	pub(super) fn report_incompatible_method_signature(
		&self,
		trait_name: SymbolU32,
		method_name: SymbolU32,
		trait_fn_index: FunctionIndex,
		impl_fn_index: FunctionIndex,
		difference: &SignatureDifference,
	) -> Diagnostic<FileId> {
		let trait_fn = &self.items.functions[usize::from(trait_fn_index)];
		let impl_fn = &self.items.functions[usize::from(impl_fn_index)];
		let fmt = self.formatter(impl_fn.namespace);
		let trait_name_str = self.interner.resolve(trait_name).unwrap();
		let method_name_str = self.interner.resolve(method_name).unwrap();
		let message = format!(
			"method `{method_name_str}` has an incompatible type for trait `{trait_name_str}`"
		);

		let (impl_span, trait_span, note) = match difference {
			SignatureDifference::TypeParameterCount { expected, found } => (
				impl_fn.name.span,
				trait_fn.name.span,
				format!(
					"expected {expected} type parameter{}, found {found}",
					if *expected == 1 { "" } else { "s" }
				),
			),
			SignatureDifference::ParameterCount { expected, found } => (
				impl_fn.name.span,
				trait_fn.name.span,
				format!(
					"expected {expected} parameter{}, found {found}",
					if *expected == 1 { "" } else { "s" }
				),
			),
			SignatureDifference::Parameter { index, difference } => (
				impl_fn.params[*index].ty.span,
				trait_fn.params[*index].ty.span,
				describe_type_difference(&fmt, difference),
			),
			SignatureDifference::ReturnType { difference } => (
				impl_fn.result.map_or(impl_fn.name.span, |r| r.span),
				trait_fn.result.map_or(trait_fn.name.span, |r| r.span),
				describe_type_difference(&fmt, difference),
			),
		};

		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplSignatureMismatch.code())
			.with_message(message)
			.with_label(
				SourceSpan::new(impl_fn.file_id, impl_span)
					.primary_label()
					.with_message(note),
			)
			.with_label(
				SourceSpan::new(trait_fn.file_id, trait_span)
					.secondary_label()
					.with_message("type in trait"),
			);
		if let SignatureDifference::Parameter { difference, .. }
		| SignatureDifference::ReturnType { difference } = difference
			&& let Some(path_note) = describe_path(&difference.path)
		{
			diagnostic = diagnostic.with_note(path_note);
		}
		diagnostic
	}

	pub(super) fn report_incompatible_const_type(
		&self,
		trait_name: SymbolU32,
		const_name: SymbolU32,
		trait_const_index: ConstIndex,
		impl_const_index: ConstIndex,
		difference: &TypeDifference,
	) -> Diagnostic<FileId> {
		let trait_const = &self.items.constants[usize::from(trait_const_index)];
		let impl_const = &self.items.constants[usize::from(impl_const_index)];
		let fmt = self.formatter(impl_const.namespace);
		let trait_name_str = self.interner.resolve(trait_name).unwrap();
		let const_name_str = self.interner.resolve(const_name).unwrap();

		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplConstTypeMismatch.code())
			.with_message(format!(
				"associated constant `{const_name_str}` has an incompatible type for trait `{trait_name_str}`"
			))
			.with_label(
				SourceSpan::new(impl_const.file_id, impl_const.ty.span)
					.primary_label()
					.with_message(describe_type_difference(&fmt, difference)),
			)
			.with_label(
				SourceSpan::new(trait_const.file_id, trait_const.ty.span)
					.secondary_label()
					.with_message("type in trait"),
			);
		if let Some(path_note) = describe_path(&difference.path) {
			diagnostic = diagnostic.with_note(path_note);
		}
		diagnostic
	}
}

/// A short, kind-specific lead-in for `expected`/`found` — most kinds read
/// fine as a plain "expected `X`, found `Y`" once both sides are formatted
/// (a pointer's ownership sigil and an array's length are already part of
/// how `display_type` prints them), but a few benefit from saying what
/// actually differs rather than making the reader diff two printed types
/// themselves.
fn describe_type_difference(
	fmt: &TypeFormatter<'_>,
	difference: &TypeDifference,
) -> String {
	let expected_str =
		fmt.display_type(difference.expected).unwrap_or_default();
	let found_str = fmt.display_type(difference.found).unwrap_or_default();
	match difference.kind {
		TypeDifferenceKind::ParameterCount => format!(
			"expected a function taking `{expected_str}`, found one taking `{found_str}`"
		),
		TypeDifferenceKind::TypeArgumentCount => format!(
			"expected `{expected_str}`, found `{found_str}` (different number of type arguments)"
		),
		TypeDifferenceKind::TupleLength => format!(
			"expected the tuple `{expected_str}`, found `{found_str}` (different length)"
		),
		TypeDifferenceKind::ArrayLength => format!(
			"expected the array `{expected_str}`, found `{found_str}` (different length)"
		),
		TypeDifferenceKind::Ownership => format!(
			"expected `{expected_str}`, found `{found_str}` (different ownership)"
		),
		TypeDifferenceKind::Nominal
		| TypeDifferenceKind::Shape
		| TypeDifferenceKind::TypeParam => {
			format!("expected `{expected_str}`, found `{found_str}`")
		}
	}
}

/// `None` for an empty path — the mismatch is already the whole
/// parameter/return/const type, nothing more specific to point at.
fn describe_path(path: &[TypePathElement]) -> Option<String> {
	if path.is_empty() {
		return None;
	}
	let steps = path
		.iter()
		.map(|element| match element {
			TypePathElement::TupleElement(index) => {
				format!("tuple element {}", index + 1)
			}
			TypePathElement::TypeArgument(index) => {
				format!("type argument {}", index + 1)
			}
			TypePathElement::FunctionParameter(index) => {
				format!("parameter {}", index + 1)
			}
			TypePathElement::FunctionResult => "return type".to_string(),
			TypePathElement::Pointee => "pointee".to_string(),
			TypePathElement::ArrayElement => "array element".to_string(),
			TypePathElement::SliceElement => "slice element".to_string(),
			TypePathElement::Memory => "memory".to_string(),
		})
		.collect::<Vec<_>>()
		.join(" -> ");
	Some(format!("specifically in {steps}"))
}
