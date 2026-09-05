//! Read-only structural comparison between a trait item's declared type and
//! the corresponding impl item's — the E0053-style "incompatible signature"
//! check `check_trait_conformance` defers to.
//!
//! The core problem this exists to avoid: `substitute_type` (generics.rs)
//! materializes a concrete instantiation as a byproduct of resolving a type,
//! which is right for the signature phase (the result is stored in TIR) but
//! wrong for conformance checking, which only ever needs a yes/no answer plus
//! a diagnostic — it shouldn't grow the type pool to get one. `compare`
//! never interns a type: instead of substituting `Self`/an impl's own
//! generics into a *new* type and comparing the result, it walks the trait
//! side's original type tree and the impl side's original type tree in
//! lockstep, resolving an abstract node to whatever it means *right here*
//! only when the walk actually reaches it.
//!
//! `TypeEnv` is what makes that possible. It answers one question — *what
//! does this abstract type variable mean right here?* — and records only the
//! two kinds of binding this comparison needs: the trait's own `Self`
//! (`TypeEnv::TraitSelf`, the base of every chain — a trait has exactly one
//! type param), and, once a projection resolves through `find_trait_impl`,
//! that one impl's own inferred type arguments (`TypeEnv::Impl`). Same idea
//! as `T` "being" `i32` inside `Vec<i32>`: one binding per generic context,
//! chained the way lexical scopes are.
//!
//! Envs live in a `TypeEnvArena` owned by the top-level `compare_*` call and
//! are referred to by a `Copy` `TypeEnvId`. The indirection is what lets a
//! resolver build a `TypeEnv::Impl` and *return* a type still pointing at it
//! — a borrowed `&TypeEnv` on the resolver's stack couldn't escape — so both
//! sides of a comparison run through the same `resolve_head`.
//!
//! A method's own generics are not put in the env at all: they're matched by
//! relative position against the *other* function's own generics (off
//! `Function::inherited_type_param_count`).

use crate::diagnostics::DiagnosticCode;

use super::*;

/// A type as interpreted "here" — a raw `index`, plus the `TypeEnvId` of the
/// environment that says what its abstract nodes mean at this point in the
/// walk. `env` is a `Copy` index into a `TypeEnvArena`, not a borrow, so a
/// `Ty` carrying a freshly-built env can be returned from a resolver. Both
/// sides of a comparison carry one and their envs are compared — see
/// `compare`'s fast path.
#[derive(Clone, Copy)]
struct Ty {
	index: TypeIndex,
	env: TypeEnvId,
}

impl Ty {
	/// A type written directly in a signature — starts under the `TraitSelf`
	/// env.
	fn at_root(index: TypeIndex) -> Self {
		Ty {
			index,
			env: TypeEnvArena::ROOT,
		}
	}
}

/// A `Copy` handle into a [`TypeEnvArena`]. Value equality is meaningful
/// here: the `TraitSelf` link is shared by both sides of a comparison, and
/// two equal `Impl` ids are the literal same `push_impl` — so `a.env ==
/// b.env` in `compare`'s fast path means "same environment".
#[derive(Clone, Copy, PartialEq, Eq)]
struct TypeEnvId(u32);

/// One link in the environment chain: a set of abstract type variables and
/// what they concretely mean here, plus a `parent` link to the enclosing
/// set.
enum TypeEnv {
	/// Binds the trait's `Self` to the impl's target type. The base of
	/// every chain; exactly one, since a trait has one type parameter. Any
	/// `TypeParamOwner::Trait(_)` reaching `resolve` is necessarily this
	/// comparison's trait — a trait item's signature references only its
	/// own `Self` — so `resolve` matches `Trait(_)` without checking which.
	TraitSelf { self_ty: TypeIndex },
	/// Binds one generic impl's type parameters to the arguments inferred
	/// for it, resolved relative to `parent`. A variable inside `args[i]`
	/// belonging to some *other* owner resolves against `parent`, not here.
	Impl {
		impl_index: TraitImplIndex,
		args: Box<[TypeIndex]>,
		parent: TypeEnvId,
	},
}

/// Owns every `TypeEnv` link built during one top-level comparison. Slot 0
/// is always the `TraitSelf` link; the arena is truncated back to just that
/// between parameters, the same way `path` is reused.
struct TypeEnvArena {
	envs: Vec<TypeEnv>,
}

impl TypeEnvArena {
	/// The always-present slot-0 link — a [`TypeEnv::TraitSelf`].
	const ROOT: TypeEnvId = TypeEnvId(0);

	fn new(self_ty: TypeIndex) -> Self {
		Self {
			envs: vec![TypeEnv::TraitSelf { self_ty }],
		}
	}

	/// Drop every `Impl` link built for the previous parameter, keeping the
	/// shared `TraitSelf`.
	fn reset(&mut self) {
		self.envs.truncate(1);
	}

	fn push_impl(
		&mut self,
		impl_index: TraitImplIndex,
		args: Box<[TypeIndex]>,
		parent: TypeEnvId,
	) -> TypeEnvId {
		let id = TypeEnvId(self.envs.len() as u32);
		self.envs.push(TypeEnv::Impl {
			impl_index,
			args,
			parent,
		});
		id
	}

	/// Resolve type variable `(owner, index)` against the env at `id`,
	/// walking `parent` links. `None` means no env in the chain binds this
	/// owner — a method-owned generic, which stays abstract.
	fn resolve(
		&self,
		id: TypeEnvId,
		owner: TypeParamOwner,
		index: u32,
	) -> Option<Ty> {
		match &self.envs[id.0 as usize] {
			TypeEnv::TraitSelf { self_ty }
				if matches!(owner, TypeParamOwner::Trait(_)) =>
			{
				Some(Ty {
					index: *self_ty,
					env: id,
				})
			}
			TypeEnv::TraitSelf { .. } => None,
			TypeEnv::Impl {
				impl_index,
				args,
				parent,
			} => {
				if owner == TypeParamOwner::TraitImpl(*impl_index) {
					Some(Ty {
						index: args[index as usize],
						env: *parent,
					})
				} else {
					self.resolve(*parent, owner, index)
				}
			}
		}
	}
}

/// A type whose meaning cannot depend on a type environment — nothing
/// nested that an env could reinterpret. For these, equal resolved indices
/// mean equal types even when the two sides were reached under different
/// envs, which is what lets `compare_structural` short-circuit a pair that
/// `compare`'s env-sensitive fast path had to let through.
fn is_env_independent(ty: &Type) -> bool {
	matches!(
		ty,
		Type::Unit
			| Type::Never
			| Type::Integer
			| Type::Float
			| Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::U64
			| Type::I64
			| Type::F32
			| Type::F64
			| Type::Bool
			| Type::Char
			| Type::Enum { .. }
			| Type::Namespace { .. }
			| Type::Memory { .. }
			| Type::AssociatedType { .. }
	)
}

/// Where the first meaningful difference occurred. `expected`/`found` are
/// always real, already-interned leaves (`compare` normalizes past any
/// `TypeParam`/`AssocTypeProjection` head before reporting a `Different`),
/// so the *kind* of difference is re-derived from them at rendering time by
/// [`TypeDifferenceKind::classify`] rather than stored.
#[derive(Clone)]
pub(super) struct TypeDifference {
	pub(super) path: Vec<TypePathElement>,
	pub(super) expected: TypeIndex,
	pub(super) found: TypeIndex,
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

pub(super) enum TypeComparison {
	Equivalent,
	Different(TypeDifference),
	/// Couldn't prove anything — an earlier type error, a missing
	/// associated-type impl, or a receiver too abstract to look anything up.
	/// Never promoted to `Different`, so it doesn't stack a second,
	/// misleading diagnostic on top of whatever already explains the gap.
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
	// No variant for bound compatibility (an impl method mustn't require
	// stricter bounds than the trait declares) — not implemented yet.
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

		let mut arena = TypeEnvArena::new(trait_impl.target.inner);
		// One `path` for the whole signature: `recurse!` always pops, so it
		// is back to empty after each `compare` (asserted below).
		let mut path = Vec::new();
		for (index, (expected, found)) in trait_fn
			.params
			.iter()
			.zip(impl_fn.params.iter())
			.enumerate()
		{
			debug_assert!(path.is_empty());
			arena.reset();
			match self.compare(
				&mut arena,
				Ty::at_root(expected.ty.inner),
				Ty::at_root(found.ty.inner),
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
		arena.reset();
		match self.compare(
			&mut arena,
			Ty::at_root(expected_result),
			Ty::at_root(found_result),
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
		let mut arena = TypeEnvArena::new(trait_impl.target.inner);
		self.compare(
			&mut arena,
			Ty::at_root(trait_const.ty.inner),
			Ty::at_root(impl_const.ty.inner),
			&mut Vec::new(),
		)
	}

	/// Compare one trait-side type against one impl-side type, each under its
	/// own type env. The recursion entry point: fast paths first, then
	/// `resolve_head` both sides symmetrically, then dispatch on the
	/// normalized heads — `compare_unresolved_type_param` when the trait
	/// side is a bare method generic, `compare_structural` otherwise.
	fn compare(
		&self,
		arena: &mut TypeEnvArena,
		expected: Ty,
		found: Ty,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		// `Error`/`Infer` sit at fixed slots, so this is a bare index
		// compare. Also re-checked inside `resolve_head` after every step;
		// this covers a side that arrives already unknowable.
		if expected.index == TypeIndex::ERROR
			|| expected.index == TypeIndex::INFER
			|| found.index == TypeIndex::ERROR
			|| found.index == TypeIndex::INFER
		{
			return TypeComparison::Indeterminate;
		}

		// Same raw type under the same env is unconditionally the same type.
		// The `env` half is load-bearing: the one interned `(T,)` reached
		// under two different `Impl` envs can mean `(i32,)` on one side and
		// `(U,)` on the other, so `index == index` alone would be a false
		// match.
		if expected.index == found.index && expected.env == found.env {
			return TypeComparison::Equivalent;
		}

		// `T::Item` vs `U::Item` for corresponding method generics `T`/`U`:
		// proven by recursing on the bases, no impl lookup. Must run before
		// `resolve_head` — a bare method generic isn't a resolvable
		// projection base and would otherwise land as `Indeterminate`.
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
		) = (
			self.types.resolve(expected.index),
			self.types.resolve(found.index),
		) && et == ft
			&& ea == fa
			&& let TypeComparison::Equivalent = self.compare(
				arena,
				Ty {
					index: eb,
					env: expected.env,
				},
				Ty {
					index: fb,
					env: found.env,
				},
				path,
			) {
			return TypeComparison::Equivalent;
		}

		let (Some(e), Some(f)) = (
			self.resolve_head(arena, expected),
			self.resolve_head(arena, found),
		) else {
			return TypeComparison::Indeterminate;
		};

		// Same fast path once more, on the normalized heads: a trait-side
		// projection can normalize straight back to the impl's own param
		// (`type Item = T` for a `Box<T>` receiver), landing on the exact
		// `Ty` `found` writes directly.
		if e.index == f.index && e.env == f.env {
			return TypeComparison::Equivalent;
		}

		// A bare `TypeParam` head on the trait side is a method generic,
		// matched positionally. Anything else — `e` concrete, or `f` still a
		// bare generic — goes to `compare_structural`, which mismatches it.
		if matches!(self.types.resolve(e.index), Type::TypeParam { .. }) {
			self.compare_unresolved_type_param(e, f, path)
		} else {
			self.compare_structural(arena, e, f, path)
		}
	}

	/// Normalize `ty` until its head is neither an env-resolvable
	/// `TypeParam` nor a resolvable `AssocTypeProjection`, and return it.
	/// `None` means normalization couldn't finish (`Error`/`Infer`, or a
	/// projection with no impl) — the caller treats it as `Indeterminate`.
	///
	/// A returned `Ty` whose `index` still resolves to a `TypeParam` is a
	/// method's own generic that no env binds; the caller re-resolves the
	/// index to tell that apart from a concrete head.
	///
	/// A chain like `Self::Mid::Out` unwinds outermost-first: the `::Out`
	/// projection resolves its base `Self::Mid` (recursively through here),
	/// then applies `::Out` to whatever that produced.
	fn resolve_head(&self, arena: &mut TypeEnvArena, mut ty: Ty) -> Option<Ty> {
		loop {
			if ty.index == TypeIndex::ERROR || ty.index == TypeIndex::INFER {
				return None;
			}
			match self.types.resolve(ty.index) {
				Type::TypeParam { owner, param_index } => {
					match arena.resolve(ty.env, *owner, *param_index) {
						Some(next) => ty = next,
						// No env binds it (a method generic) — `ty` is the head.
						None => return Some(ty),
					}
				}
				Type::AssocTypeProjection {
					base,
					trait_index,
					assoc_name,
				} => {
					let (base, trait_index, assoc_name) =
						(*base, *trait_index, *assoc_name);
					let base = self.resolve_head(
						arena,
						Ty {
							index: base,
							env: ty.env,
						},
					)?;
					ty = self.project(arena, base, trait_index, assoc_name)?;
				}
				_ => return Some(ty),
			}
		}
	}

	/// One `base::<trait_index>::assoc_name` step, `base` already
	/// head-normalized. A declared `where { assoc_name = T }` on `base`'s
	/// own bounds proves it without an impl (the only way an abstract base
	/// resolves, and a shortcut for a concrete one); otherwise the concrete
	/// impl is looked up and its inferred arguments pushed as a new env.
	/// `None` — no impl, or the impl omits this associated type — is
	/// "couldn't prove," surfaced by the caller as `Indeterminate`, never a
	/// `Different`.
	fn project(
		&self,
		arena: &mut TypeEnvArena,
		base: Ty,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Option<Ty> {
		if let Some(bound_value) = self.resolve_projection_via_bound(
			base.index,
			trait_index,
			assoc_name,
		) {
			// The binding's value is written in `base`'s own scope.
			return Some(Ty {
				index: bound_value,
				env: base.env,
			});
		}
		let (impl_index, impl_args) =
			self.items
				.find_trait_impl(&self.types, base.index, trait_index)?;
		let ImplEntry::AssocType(assoc_idx) = self.items.trait_impls
			[usize::from(impl_index)]
		.members
		.get(&assoc_name)?
		else {
			return None;
		};
		// The impl's written value, still in terms of the impl's own params
		// — hence the new `push_impl` env below.
		let raw = self.items.assoc_type_impls[usize::from(*assoc_idx)]
			.ty?
			.inner;
		let env = arena.push_impl(impl_index, impl_args, base.env);
		// Runaway guard, not a real cycle check: a cyclic associated-type
		// value is already `ERROR` from Phase 2 (see
		// `test_self_referential_assoc_type_value_does_not_hang_or_cascade`),
		// so `resolve_head` bails before it can loop back here. Fires only if
		// that stops holding.
		debug_assert!(
			arena.envs.len() < 10_000,
			"projection resolution exceeded 10k type-env links — a cyclic \
			 associated-type value reached conformance checking unreduced"
		);
		Some(Ty { index: raw, env })
	}

	/// `expected` normalized to a bare `TypeParam` no env binds — on the
	/// trait side that is always a method's own generic (`Self` resolves via
	/// `TypeEnv::TraitSelf`; a trait signature has no impl-owned params). It
	/// matches only a `found` that is the impl method's own generic at the
	/// same position relative to `inherited_type_param_count`; anything else
	/// is a mismatch. Since a signature can only name its own generic scope,
	/// the two `Function` owners seen here are exactly this trait method's
	/// and this impl method's.
	fn compare_unresolved_type_param(
		&self,
		expected: Ty,
		found: Ty,
		path: &[TypePathElement],
	) -> TypeComparison {
		let mismatch = || {
			TypeComparison::Different(TypeDifference {
				path: path.to_vec(),
				expected: expected.index,
				found: found.index,
			})
		};
		let (
			&Type::TypeParam {
				owner: TypeParamOwner::Function(expected_fn),
				param_index: expected_index,
			},
			&Type::TypeParam {
				owner: TypeParamOwner::Function(found_fn),
				param_index: found_index,
			},
		) = (
			self.types.resolve(expected.index),
			self.types.resolve(found.index),
		)
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

	/// Look through `base`'s declared bounds for a `where { assoc_name = T }`
	/// equality binding on `trait_index` — this is what proves `T::Item`
	/// equal to `i32` given `T: Container where { Item = i32 }`, with no
	/// concrete impl for `T`.
	fn resolve_projection_via_bound(
		&self,
		base: TypeIndex,
		trait_index: TraitIndex,
		assoc_name: SymbolU32,
	) -> Option<TypeIndex> {
		let bounds = self.items.abstract_type_bounds(&self.types, base)?;
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

	fn compare_structural(
		&self,
		arena: &mut TypeEnvArena,
		expected: Ty,
		found: Ty,
		path: &mut Vec<TypePathElement>,
	) -> TypeComparison {
		macro_rules! recurse {
			($element:expr, $e:expr, $f:expr) => {{
				path.push($element);
				let result = self.compare(
					arena,
					Ty {
						index: $e,
						env: expected.env,
					},
					Ty {
						index: $f,
						env: found.env,
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
			// Same leaf type, different envs (equal envs already handled by
			// `compare`). Nothing an env could reinterpret — so, equal.
			(a, b) if a == b && is_env_independent(a) => {
				TypeComparison::Equivalent
			}
			(Type::Tuple { elements: e }, Type::Tuple { elements: f }) => {
				if e.len() != f.len() {
					return self.different(expected, found, path);
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
					return self.different(expected, found, path);
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
				if eown != fown || es != fs {
					return self.different(expected, found, path);
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
					return self.different(expected, found, path);
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
				if esi != fsi || ea.len() != fa.len() {
					return self.different(expected, found, path);
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
					return self.different(expected, found, path);
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
					return self.different(expected, found, path);
				}
				for (index, (&ei, &fi)) in ea.iter().zip(fa.iter()).enumerate()
				{
					recurse!(TypePathElement::TypeArgument(index), ei, fi);
				}
				TypeComparison::Equivalent
			}
			_ => self.different(expected, found, path),
		}
	}

	fn different(
		&self,
		expected: Ty,
		found: Ty,
		path: &[TypePathElement],
	) -> TypeComparison {
		TypeComparison::Different(TypeDifference {
			path: path.to_vec(),
			expected: expected.index,
			found: found.index,
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
				describe_type_difference(&fmt, &self.types, difference),
			),
			SignatureDifference::ReturnType { difference } => (
				impl_fn.result.map_or(impl_fn.name.span, |r| r.span),
				trait_fn.result.map_or(trait_fn.name.span, |r| r.span),
				describe_type_difference(&fmt, &self.types, difference),
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
					.with_message(describe_type_difference(&fmt, &self.types, difference)),
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

/// Vocabulary for the diagnostic lead-in only — produced by
/// [`TypeDifferenceKind::classify`] from the two leaf types, consumed by
/// [`describe_type_difference`]. Never stored.
#[derive(Clone, Copy)]
pub(super) enum TypeDifferenceKind {
	Shape,
	Nominal,
	Ownership,
	ArrayLength,
	TupleLength,
	ParameterCount,
	TypeArgumentCount,
}

impl TypeDifferenceKind {
	/// Re-derive the kind of difference from the two leaf types the walk
	/// stopped on. Arm order mirrors `compare_structural`'s own check order
	/// (ownership before length, nominal before argument count).
	fn classify(expected: &Type, found: &Type) -> Self {
		match (expected, found) {
			(
				Type::Struct {
					struct_index: a, ..
				},
				Type::Struct {
					struct_index: b, ..
				},
			) if a != b => Self::Nominal,
			(Type::Struct { args: a, .. }, Type::Struct { args: b, .. })
				if a.len() != b.len() =>
			{
				Self::TypeArgumentCount
			}
			(Type::Enum { enum_index: a }, Type::Enum { enum_index: b })
				if a != b =>
			{
				Self::Nominal
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
			) if a != b => Self::Ownership,
			(Type::Array { size: a, .. }, Type::Array { size: b, .. })
				if a != b =>
			{
				Self::ArrayLength
			}
			(Type::Tuple { elements: a }, Type::Tuple { elements: b })
				if a.len() != b.len() =>
			{
				Self::TupleLength
			}
			(
				Type::FunctionItem { id: a, .. },
				Type::FunctionItem { id: b, .. },
			) if a != b => Self::Nominal,
			(
				Type::Function { signature: a },
				Type::Function { signature: b },
			) if a.params().len() != b.params().len() => Self::ParameterCount,
			_ => Self::Shape,
		}
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
	types: &TypeInterner,
	difference: &TypeDifference,
) -> String {
	let expected_str =
		fmt.display_type(difference.expected).unwrap_or_default();
	let found_str = fmt.display_type(difference.found).unwrap_or_default();
	let kind = TypeDifferenceKind::classify(
		types.resolve(difference.expected),
		types.resolve(difference.found),
	);
	match kind {
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
		TypeDifferenceKind::Nominal | TypeDifferenceKind::Shape => {
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
