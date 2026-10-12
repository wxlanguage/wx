//! Associated-type normalization. Declaration identity stays in projections;
//! abstract equalities come from effective bounds; concrete values come from
//! selected impl providers. Evidence comparison uses the same traversal and
//! budget, reducing assumed equalities without selecting providers.
//! Structural substitution remains independent in `types.rs`.

use codespan_reporting::diagnostic::Diagnostic;

use crate::diagnostics::{DiagnosticCode, SourceSpan};

use super::assumptions::{AssumptionContext, QueryError, QueryResult};
use super::bounds::EqualityLookup;
use super::defs::{AssocTypeIdx, MemberKind, TraitIdx};
use super::members::{TraitImplLookup, TraitMemberSelection};
use super::obligations::Obligation;
use super::signatures::TypeContext;
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex};

struct ProjectionFrame {
	// Evidence comparison and provider reduction have distinct cycle keys.
	mode: Mode,
	context: AssumptionContext,
	projection: TypeIndex,
	reference: SourceSpan,
	assumed: bool,
}

/// Shared across re-entrant signature queries, not recreated per API call.
/// No completed-result cache: bounds and inference are still being built.
pub(super) struct NormalizationState {
	active: Vec<ProjectionFrame>,
	depth: usize,
	limit: usize,
	failed: bool,
	/// Roll back an assumed equality chain that made no finite progress.
	blocked_at: Option<usize>,
}

impl Default for NormalizationState {
	fn default() -> Self {
		Self {
			active: Vec::new(),
			depth: 0,
			limit: 128,
			failed: false,
			blocked_at: None,
		}
	}
}

impl NormalizationState {
	/// Bound readers traverse receiver structure within the same work limit.
	pub(super) fn remaining_depth(&self) -> usize {
		self.limit - self.depth
	}
}

#[cfg(test)]
impl NormalizationState {
	pub(super) fn set_limit_for_test(&mut self, limit: usize) {
		self.limit = limit;
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
	Head,
	Deep,
	/// Reduce only assumed equalities, including nested type structure.
	/// Comparing evidence must not recursively select the impl being proved.
	Assumptions,
}

impl TypeContext<'_, '_, '_> {
	/// Budget exhaustion is a diagnosed failure, never an unfinished fact.
	/// Poison an active normalization only; a top-level proof can be retried.
	pub(super) fn normalization_overflow(
		&mut self,
		reference: SourceSpan,
	) -> QueryError {
		if !self.normalization.failed {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeNormalizationOverflow.code())
					.with_message(
						"type normalization exceeded its recursion limit",
					)
					.with_label(reference.primary_label()),
			);
		}
		if self.normalization.depth > 0 {
			self.normalization.failed = true;
		}
		QueryError::Failed
	}

	/// Construction keeps unfinished reductions symbolic and records the
	/// work on the declaration being built. Proof consumers use the query API.
	pub(super) fn normalize_head(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> TypeIndex {
		self.normalization_value(cx, ty, reference, Mode::Head)
	}

	pub(super) fn normalize_type(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> TypeIndex {
		self.normalization_value(cx, ty, reference, Mode::Deep)
	}

	fn normalization_value(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> TypeIndex {
		match self.normalize(cx, ty, reference, mode) {
			Ok(result) => result,
			Err(QueryError::Failed) => TypeIndex::ERROR,
			Err(QueryError::Pending) => {
				self.register_obligation(Obligation::Normalize {
					context: cx,
					subject: ty,
					reference,
				});
				ty
			}
		}
	}

	/// A ready result can be an abstract projection. Pending is a dependency
	/// state, never evidence that a concrete impl does not match.
	pub(super) fn normalize_head_query(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> QueryResult<TypeIndex> {
		self.normalize(cx, ty, reference, Mode::Head)
	}

	pub(super) fn normalize_type_query(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> QueryResult<TypeIndex> {
		self.normalize(cx, ty, reference, Mode::Deep)
	}

	pub(super) fn normalize_assumed_type_query(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> QueryResult<TypeIndex> {
		self.normalize(cx, ty, reference, Mode::Assumptions)
	}

	fn normalize(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> QueryResult<TypeIndex> {
		if self.normalization.failed {
			return Err(QueryError::Failed);
		}
		if self.normalization.blocked_at.is_some() {
			return Ok(ty);
		}
		if self.normalization.depth == self.normalization.limit {
			return Err(self.normalization_overflow(reference));
		}
		self.normalization.depth += 1;
		let result = if matches!(
			self.types.resolve(ty),
			Type::AssocTypeProjection { .. }
		) {
			self.normalize_projection(cx, ty, reference, mode)
		} else {
			match mode {
				Mode::Head => Ok(ty),
				Mode::Deep | Mode::Assumptions => {
					self.normalize_children(cx, ty, reference, mode)
				}
			}
		};
		self.normalization.depth -= 1;
		let result = if self.normalization.failed {
			Err(QueryError::Failed)
		} else {
			result
		};
		if self.normalization.depth == 0 {
			debug_assert!(self.normalization.active.is_empty());
			debug_assert!(self.normalization.blocked_at.is_none());
			self.normalization.failed = false;
		}
		result
	}

	fn normalize_projection(
		&mut self,
		cx: AssumptionContext,
		projection: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> QueryResult<TypeIndex> {
		if self.projection_cycle(cx, projection, reference, mode) {
			return if self.normalization.failed {
				Err(QueryError::Failed)
			} else {
				Ok(projection)
			};
		}
		self.normalization.active.push(ProjectionFrame {
			mode,
			context: cx,
			projection,
			reference,
			assumed: false,
		});
		// Keep the frame active across receiver normalization, provider queries,
		// and traversal of the resulting type, including compound results.
		let result = self.reduce_projection(cx, projection, reference, mode);
		let index = self.normalization.active.len() - 1;
		self.normalization.active.pop();
		if let Some(blocked) = self.normalization.blocked_at {
			if index == blocked {
				self.normalization.blocked_at = None;
			}
			return Ok(projection);
		}
		result
	}

	fn reduce_projection(
		&mut self,
		cx: AssumptionContext,
		projection: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> QueryResult<TypeIndex> {
		let Type::AssocTypeProjection {
			base,
			trait_index,
			assoc_type_index,
		} = *self.types.resolve(projection)
		else {
			unreachable!()
		};
		// Receiver-specific nested facts must be read before reducing the
		// receiver to a value that no longer carries their provenance.
		if let Some(result) = self.reduce_assumed_projection(
			cx,
			projection,
			base,
			trait_index,
			assoc_type_index,
			reference,
			mode,
		)? {
			return Ok(result);
		}
		let next_base = self.normalize(cx, base, reference, mode)?;
		if next_base == TypeIndex::ERROR {
			return Err(QueryError::Failed);
		}
		let projection = if next_base == base {
			projection
		} else {
			let next = self.types.intern(Type::AssocTypeProjection {
				base: next_base,
				trait_index,
				assoc_type_index,
			});
			if self.projection_cycle(cx, next, reference, mode) {
				return if self.normalization.failed {
					Err(QueryError::Failed)
				} else {
					Ok(projection)
				};
			}
			self.normalization.active.last_mut().unwrap().projection = next;
			next
		};
		if matches!(
			self.types.resolve(next_base),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return Ok(self
				.reduce_assumed_projection(
					cx,
					projection,
					next_base,
					trait_index,
					assoc_type_index,
					reference,
					mode,
				)?
				.unwrap_or(projection));
		}
		if matches!(
			self.types.resolve(next_base),
			Type::Infer | Type::AssociatedType { .. }
		) {
			return Ok(projection);
		}
		if mode == Mode::Assumptions {
			return Ok(projection);
		}
		let Some(found) =
			self.find_trait_impl_query(cx, next_base, trait_index, reference)?
		else {
			let diagnostic = self.report_type_does_not_implement_trait(
				reference.file_id,
				reference.span,
				next_base,
				trait_index,
			);
			self.diagnostics.push(diagnostic);
			return Err(QueryError::Failed);
		};
		let TraitImplLookup::Concrete { impl_index, args } = found else {
			return Ok(projection);
		};
		let selection = self.defs.select_trait_member(
			impl_index,
			MemberKind::AssociatedType(assoc_type_index),
		);
		let instantiated = match selection {
			TraitMemberSelection::Impl(MemberKind::AssociatedType(
				provider,
			)) => {
				let value =
					self.ensure_assoc_type_value_query(provider, reference)?;
				if args.is_empty() {
					value
				} else {
					let env = self.trait_impls[usize::from(impl_index)]
						.as_ref()
						.expect("a generic selected impl has a resolved header")
						.type_params;
					debug_assert_ne!(env, TypeEnvIdx::ROOT);
					self.types
						.substitute(value, &Substitution { env, args: &args })
				}
			}
			TraitMemberSelection::Impl(_) => return Err(QueryError::Failed),
			TraitMemberSelection::TraitDeclaration(_) => {
				let Some(value) = self.ensure_assoc_type_default_value_query(
					assoc_type_index,
					reference,
				)?
				else {
					// The later conformance pass owns missing-member diagnostics.
					return Err(QueryError::Failed);
				};
				let env = self.traits[usize::from(trait_index)].env;
				self.types.substitute(
					value,
					&Substitution {
						env,
						args: &[next_base],
					},
				)
			}
		};
		self.normalize(cx, instantiated, reference, mode)
	}

	fn reduce_assumed_projection(
		&mut self,
		cx: AssumptionContext,
		projection: TypeIndex,
		base: TypeIndex,
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
		reference: SourceSpan,
		mode: Mode,
	) -> QueryResult<Option<TypeIndex>> {
		if !matches!(
			self.types.resolve(base),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return Ok(None);
		}
		match self.projection_equality(
			cx,
			base,
			trait_index,
			assoc_type_index,
			reference,
		) {
			Ok(EqualityLookup::Known(value)) if value != projection => {
				self.normalization.active.last_mut().unwrap().assumed = true;
				self.normalize(cx, value, reference, mode).map(Some)
			}
			Ok(EqualityLookup::Known(_)) => Ok(Some(projection)),
			Ok(EqualityLookup::Pending) => Err(QueryError::Pending),
			Ok(_) => Ok(None),
			Err(()) => Err(QueryError::Failed),
		}
	}

	fn projection_cycle(
		&mut self,
		cx: AssumptionContext,
		projection: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> bool {
		let Some(start) = self.normalization.active.iter().position(|frame| {
			frame.context == cx
				&& frame.projection == projection
				&& frame.mode == mode
		}) else {
			return false;
		};
		if self.normalization.active[start..]
			.iter()
			.any(|frame| frame.assumed)
		{
			self.normalization.blocked_at = Some(
				self.normalization
					.blocked_at
					.map_or(start, |previous| previous.min(start)),
			);
			return true;
		}
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::CyclicAssociatedType.code())
			.with_message(format!(
				"cycle detected when normalizing `{}`",
				self.type_formatter().display_type(projection)
			))
			.with_label(reference.primary_label());
		for frame in &self.normalization.active[start..] {
			diagnostic = diagnostic.with_label(
				frame.reference.secondary_label().with_message(format!(
					"requires normalizing `{}`",
					self.type_formatter().display_type(frame.projection)
				)),
			);
		}
		self.diagnostics.push(diagnostic);
		self.normalization.failed = true;
		true
	}

	fn normalize_children(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> QueryResult<TypeIndex> {
		match self.types.resolve(ty) {
			Type::Tuple { .. } => {
				let elements =
					self.normalize_list(cx, ty, reference, mode, |ty| {
						let Type::Tuple { elements } = ty else {
							unreachable!()
						};
						elements
					})?;
				match elements {
					Some(elements) => {
						Ok(self.types.intern(Type::Tuple { elements }))
					}
					None => Ok(ty),
				}
			}
			Type::Struct { struct_index, .. } => {
				let struct_index = *struct_index;
				let type_args =
					self.normalize_list(cx, ty, reference, mode, |ty| {
						let Type::Struct { type_args, .. } = ty else {
							unreachable!()
						};
						type_args
					})?;
				match type_args {
					Some(type_args) => Ok(self.types.intern(Type::Struct {
						struct_index,
						type_args,
					})),
					None => Ok(ty),
				}
			}
			Type::FunctionItem { func_index, .. } => {
				let func_index = *func_index;
				let type_args =
					self.normalize_list(cx, ty, reference, mode, |ty| {
						let Type::FunctionItem { type_args, .. } = ty else {
							unreachable!()
						};
						type_args
					})?;
				match type_args {
					Some(type_args) => {
						Ok(self.types.intern(Type::FunctionItem {
							func_index,
							type_args,
						}))
					}
					None => Ok(ty),
				}
			}
			Type::Function { result, .. } => {
				let result = *result;
				let params =
					self.normalize_list(cx, ty, reference, mode, |ty| {
						let Type::Function { params, .. } = ty else {
							unreachable!()
						};
						params
					})?;
				let next_result =
					self.normalize(cx, result, reference, mode)?;
				if params.is_none() && next_result == result {
					return Ok(ty);
				}
				// A changed result still needs an owned parameter list, even
				// when none of those parameters changed.
				let params = params.unwrap_or_else(|| {
					let Type::Function { params, .. } = self.types.resolve(ty)
					else {
						unreachable!()
					};
					params.clone()
				});
				Ok(self.types.intern(Type::Function {
					params,
					result: next_result,
				}))
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				let (to, memory, ownership) = (*to, *memory, *ownership);
				let next_to = self.normalize(cx, to, reference, mode)?;
				let next_memory =
					self.normalize(cx, memory, reference, mode)?;
				if next_to == to && next_memory == memory {
					Ok(ty)
				} else {
					Ok(self.types.intern(Type::Pointer {
						to: next_to,
						memory: next_memory,
						ownership,
					}))
				}
			}
			Type::Array {
				of,
				size,
				memory,
				ownership,
			} => {
				let (of, size, memory, ownership) =
					(*of, *size, *memory, *ownership);
				let next_of = self.normalize(cx, of, reference, mode)?;
				let next_memory =
					self.normalize(cx, memory, reference, mode)?;
				if next_of == of && next_memory == memory {
					Ok(ty)
				} else {
					Ok(self.types.intern(Type::Array {
						of: next_of,
						size,
						memory: next_memory,
						ownership,
					}))
				}
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				let (of, memory, ownership) = (*of, *memory, *ownership);
				let next_of = self.normalize(cx, of, reference, mode)?;
				let next_memory =
					self.normalize(cx, memory, reference, mode)?;
				if next_of == of && next_memory == memory {
					Ok(ty)
				} else {
					Ok(self.types.intern(Type::Slice {
						of: next_of,
						memory: next_memory,
						ownership,
					}))
				}
			}
			Type::AssocTypeProjection { .. } => unreachable!(
				"projections are handled before structural traversal"
			),
			Type::Error
			| Type::Infer
			| Type::Unit
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
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::AssociatedType { .. }
			| Type::TypeParam { .. } => Ok(ty),
		}
	}

	/// Allocate output storage only after the first changed child.
	fn normalize_list(
		&mut self,
		cx: AssumptionContext,
		ty: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
		list: impl Fn(&Type) -> &[TypeIndex],
	) -> QueryResult<Option<Box<[TypeIndex]>>> {
		let len = list(self.types.resolve(ty)).len();
		let mut normalized: Option<Box<[TypeIndex]>> = None;
		for index in 0..len {
			let original = list(self.types.resolve(ty))[index];
			let next = self.normalize(cx, original, reference, mode)?;
			if next != original {
				let items = normalized.get_or_insert_with(|| {
					Box::from(list(self.types.resolve(ty)))
				});
				items[index] = next;
			}
			if self.normalization.failed {
				break;
			}
		}
		Ok(normalized)
	}
}
