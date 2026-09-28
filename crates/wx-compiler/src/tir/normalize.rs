//! Associated-type normalization. Declaration identity stays in projections;
//! abstract equalities come from effective bounds; concrete values come from
//! selected impl providers.
//! Structural substitution remains independent in `types.rs`.

use codespan_reporting::diagnostic::Diagnostic;

use crate::diagnostics::{DiagnosticCode, SourceSpan};

use super::bounds::EqualityLookup;
use super::defs::{AssocTypeIdx, TraitIdx};
use super::members::TraitImplLookup;
use super::signatures::SignatureBuilder;
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex};

struct ProjectionFrame {
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

	/// Poisons the rest of the active normalization the same way the
	/// recursion-limit check in `normalize` does, for a failure diagnosed
	/// outside this module (bound-fact readers sharing the same work limit).
	/// Short-circuits sibling branches still to be visited in this call —
	/// e.g. other elements of a tuple mid-`normalize_list` — instead of
	/// letting each rediscover and re-diagnose the same overflow.
	pub(super) fn mark_failed(&mut self) {
		self.failed = true;
	}
}

#[cfg(test)]
impl NormalizationState {
	pub(super) fn set_limit_for_test(&mut self, limit: usize) {
		self.limit = limit;
	}
}

#[derive(Clone, Copy)]
enum Mode {
	Head,
	Deep,
}

impl SignatureBuilder<'_, '_> {
	/// Exposes the outer constructor, leaving its children untouched.
	/// Abstract projections and inference are valid unreduced results.
	pub(super) fn normalize_head(
		&mut self,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> TypeIndex {
		self.normalize(ty, reference, Mode::Head)
	}

	/// Normalizes projections throughout the type, without expanding nominal
	/// definitions. Unchanged child lists are borrowed, never cloned.
	pub(super) fn normalize_type(
		&mut self,
		ty: TypeIndex,
		reference: SourceSpan,
	) -> TypeIndex {
		self.normalize(ty, reference, Mode::Deep)
	}

	fn normalize(
		&mut self,
		ty: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> TypeIndex {
		if self.normalization.failed {
			return TypeIndex::ERROR;
		}
		if self.normalization.blocked_at.is_some() {
			return ty;
		}
		if self.normalization.depth == self.normalization.limit {
			self.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::TypeNormalizationOverflow.code())
					.with_message(
						"type normalization exceeded its recursion limit",
					)
					.with_label(reference.primary_label()),
			);
			self.normalization.failed = true;
			return TypeIndex::ERROR;
		}
		self.normalization.depth += 1;
		let result = if matches!(
			self.types.resolve(ty),
			Type::AssocTypeProjection { .. }
		) {
			self.normalize_projection(ty, reference, mode)
		} else {
			match mode {
				Mode::Head => ty,
				Mode::Deep => self.normalize_children(ty, reference),
			}
		};
		self.normalization.depth -= 1;
		let result = if self.normalization.failed {
			TypeIndex::ERROR
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
		projection: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> TypeIndex {
		if self.projection_cycle(projection, reference) {
			return if self.normalization.failed {
				TypeIndex::ERROR
			} else {
				projection
			};
		}
		self.normalization.active.push(ProjectionFrame {
			projection,
			reference,
			assumed: false,
		});
		// Keep the frame active across receiver normalization, provider queries,
		// and traversal of the resulting type, including compound results.
		let result = self.reduce_projection(projection, reference, mode);
		let index = self.normalization.active.len() - 1;
		self.normalization.active.pop();
		if let Some(blocked) = self.normalization.blocked_at {
			if index == blocked {
				self.normalization.blocked_at = None;
			}
			return projection;
		}
		result
	}

	fn reduce_projection(
		&mut self,
		projection: TypeIndex,
		reference: SourceSpan,
		mode: Mode,
	) -> TypeIndex {
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
			projection,
			base,
			trait_index,
			assoc_type_index,
			reference,
			mode,
		) {
			return result;
		}
		let next_base = self.normalize(base, reference, mode);
		if next_base == TypeIndex::ERROR {
			return TypeIndex::ERROR;
		}
		let projection = if next_base == base {
			projection
		} else {
			let next = self.types.intern(Type::AssocTypeProjection {
				base: next_base,
				trait_index,
				assoc_type_index,
			});
			if self.projection_cycle(next, reference) {
				return if self.normalization.failed {
					TypeIndex::ERROR
				} else {
					projection
				};
			}
			self.normalization.active.last_mut().unwrap().projection = next;
			next
		};
		if matches!(
			self.types.resolve(next_base),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return self
				.reduce_assumed_projection(
					projection,
					next_base,
					trait_index,
					assoc_type_index,
					reference,
					mode,
				)
				.unwrap_or(projection);
		}
		if matches!(
			self.types.resolve(next_base),
			Type::Infer | Type::AssociatedType { .. }
		) {
			return projection;
		}
		let Ok(found) = self.find_trait_impl(
			next_base,
			trait_index,
			reference.file_id,
			reference.span,
		) else {
			return TypeIndex::ERROR;
		};
		let TraitImplLookup::Concrete { impl_index, args } = found else {
			return projection;
		};
		let Some(provider) =
			self.assoc_type_provider(impl_index, assoc_type_index)
		else {
			// The later conformance pass owns missing-member diagnostics.
			return TypeIndex::ERROR;
		};
		let value = self.ensure_assoc_type_value(provider, reference);
		let instantiated = if args.is_empty() {
			value
		} else {
			let env = self.trait_impls[usize::from(impl_index)]
				.as_ref()
				.expect("a generic selected impl has a resolved header")
				.type_params;
			debug_assert_ne!(env, TypeEnvIdx::ROOT);
			self.types
				.substitute(value, &Substitution { env, args: &args })
		};
		self.normalize(instantiated, reference, mode)
	}

	fn reduce_assumed_projection(
		&mut self,
		projection: TypeIndex,
		base: TypeIndex,
		trait_index: TraitIdx,
		assoc_type_index: AssocTypeIdx,
		reference: SourceSpan,
		mode: Mode,
	) -> Option<TypeIndex> {
		if !matches!(
			self.types.resolve(base),
			Type::TypeParam { .. } | Type::AssocTypeProjection { .. }
		) {
			return None;
		}
		match self.projection_equality(
			base,
			trait_index,
			assoc_type_index,
			reference,
		) {
			Ok(EqualityLookup::Known(value)) if value != projection => {
				self.normalization.active.last_mut().unwrap().assumed = true;
				Some(self.normalize(value, reference, mode))
			}
			Ok(EqualityLookup::Known(_)) => Some(projection),
			Ok(_) => None,
			Err(()) => Some(TypeIndex::ERROR),
		}
	}

	fn projection_cycle(
		&mut self,
		projection: TypeIndex,
		reference: SourceSpan,
	) -> bool {
		let Some(start) = self
			.normalization
			.active
			.iter()
			.position(|frame| frame.projection == projection)
		else {
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
		ty: TypeIndex,
		reference: SourceSpan,
	) -> TypeIndex {
		match self.types.resolve(ty) {
			Type::Tuple { .. } => {
				let elements = self.normalize_list(ty, reference, |ty| {
					let Type::Tuple { elements } = ty else {
						unreachable!()
					};
					elements
				});
				match elements {
					Some(elements) => {
						self.types.intern(Type::Tuple { elements })
					}
					None => ty,
				}
			}
			Type::Struct { struct_index, .. } => {
				let struct_index = *struct_index;
				let type_args = self.normalize_list(ty, reference, |ty| {
					let Type::Struct { type_args, .. } = ty else {
						unreachable!()
					};
					type_args
				});
				match type_args {
					Some(type_args) => self.types.intern(Type::Struct {
						struct_index,
						type_args,
					}),
					None => ty,
				}
			}
			Type::FunctionItem { func_index, .. } => {
				let func_index = *func_index;
				let type_args = self.normalize_list(ty, reference, |ty| {
					let Type::FunctionItem { type_args, .. } = ty else {
						unreachable!()
					};
					type_args
				});
				match type_args {
					Some(type_args) => self.types.intern(Type::FunctionItem {
						func_index,
						type_args,
					}),
					None => ty,
				}
			}
			Type::Function { result, .. } => {
				let result = *result;
				let params = self.normalize_list(ty, reference, |ty| {
					let Type::Function { params, .. } = ty else {
						unreachable!()
					};
					params
				});
				let next_result = self.normalize_type(result, reference);
				if params.is_none() && next_result == result {
					return ty;
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
				self.types.intern(Type::Function {
					params,
					result: next_result,
				})
			}
			Type::Pointer {
				to,
				memory,
				ownership,
			} => {
				let (to, memory, ownership) = (*to, *memory, *ownership);
				let next_to = self.normalize_type(to, reference);
				let next_memory = self.normalize_type(memory, reference);
				if next_to == to && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Pointer {
						to: next_to,
						memory: next_memory,
						ownership,
					})
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
				let next_of = self.normalize_type(of, reference);
				let next_memory = self.normalize_type(memory, reference);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Array {
						of: next_of,
						size,
						memory: next_memory,
						ownership,
					})
				}
			}
			Type::Slice {
				of,
				memory,
				ownership,
			} => {
				let (of, memory, ownership) = (*of, *memory, *ownership);
				let next_of = self.normalize_type(of, reference);
				let next_memory = self.normalize_type(memory, reference);
				if next_of == of && next_memory == memory {
					ty
				} else {
					self.types.intern(Type::Slice {
						of: next_of,
						memory: next_memory,
						ownership,
					})
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
			| Type::TypeParam { .. } => ty,
		}
	}

	/// Allocate output storage only after the first changed child.
	fn normalize_list(
		&mut self,
		ty: TypeIndex,
		reference: SourceSpan,
		list: impl Fn(&Type) -> &[TypeIndex],
	) -> Option<Box<[TypeIndex]>> {
		let len = list(self.types.resolve(ty)).len();
		let mut normalized: Option<Box<[TypeIndex]>> = None;
		for index in 0..len {
			let original = list(self.types.resolve(ty))[index];
			let next = self.normalize_type(original, reference);
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
		normalized
	}
}
