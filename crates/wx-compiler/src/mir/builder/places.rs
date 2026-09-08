use super::super::*;

impl<'tir> Builder<'tir> {
	/// Compute the address of a place, returning `(base_ptr, static_byte_offset, memory_id)`.
	///
	/// The caller emits a `PointerLoad`/`PointerStore` using the returned triple.
	///
	/// - `Deref { pointer }` — evaluate the pointer expression; offset = 0.
	/// - `Field { object, member }` — recurse on the parent place and add the
	///   field's static byte offset.
	/// - `Index { object, index }` — delegate to `lower_index_address`; the
	///   returned pointer already encodes runtime index arithmetic when needed.
	pub(in crate::mir) fn lower_place_address(
		&mut self,
		func_ctx: &mut FunctionContext,
		place: &tir::Place,
		sink: &mut Vec<Expression>,
	) -> (Expression, u32, ast::DefId) {
		let memory_id = self.resolve_memory_id(place.memory);
		match &place.kind {
			tir::PlaceKind::Deref { pointer } => {
				let ptr = self.lower_expression(func_ctx, pointer, sink);
				(ptr, 0, memory_id)
			}
			tir::PlaceKind::Field { object, member } => {
				let (base_ptr, base_offset, memory_id) =
					self.lower_place_address(func_ctx, object, sink);
				let (struct_index, args) = self.instantiate_struct(object.ty);
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let decl_index = usize::from(
					self.tir.items.structs[usize::from(struct_index)].lookup
						[&member.inner],
				);
				let aggregate = self.aggregate(aggregate_index);
				let field_offset =
					aggregate.field(aggregate.physical(decl_index)).offset;
				(base_ptr, base_offset + field_offset, memory_id)
			}
			tir::PlaceKind::Index { object, index } => {
				let elem_ty = place.ty;
				match self
					.lower_index_address(func_ctx, object, index, elem_ty, sink)
				{
					IndexAddress::Constant { ptr, byte_offset } => {
						(ptr, byte_offset, memory_id)
					}
					IndexAddress::Dynamic(ptr) => (ptr, 0, memory_id),
				}
			}
		}
	}

	pub(in crate::mir) fn lower_assignment(
		&mut self,
		func_ctx: &mut FunctionContext,
		left: &tir::Expression,
		right: &tir::Expression,
		sink: &mut Vec<Expression>,
	) -> ExprKind {
		if let tir::ExprKind::Placeholder = &left.kind {
			// `_ = expr`: evaluate rhs for side effects, discard the value.
			return ExprKind::Drop {
				value: Box::new(self.lower_expression(func_ctx, right, sink)),
			};
		}
		let value = self.lower_expression(func_ctx, right, sink);
		self.lower_assign_target(left, value)
	}

	/// Builds the `LocalSet`/`GlobalSet`/`AggregateSet` that writes `value`
	/// to `target` (a `Local`/`Global`/`FieldAccess`). Shared by plain
	/// assignment (`lower_assignment`, `value` = the lowered rhs) and
	/// compound assignment (`lower_compound_assign`, `value` = the resolved
	/// operator method's `Call`) — `target`'s own indices/field-offset are
	/// pure metadata lookups, never requiring further lowering, so both
	/// callers can share this exactly.
	fn lower_assign_target(
		&mut self,
		target: &tir::Expression,
		value: Expression,
	) -> ExprKind {
		match &target.kind {
			tir::ExprKind::Local {
				scope_index,
				local_index,
			} => ExprKind::LocalSet {
				scope_index: ScopeIndex::new(u32::from(*scope_index)),
				local_index: LocalIndex::new(u32::from(*local_index)),
				value: Box::new(value),
			},
			tir::ExprKind::Global { id } => ExprKind::GlobalSet {
				id: *id,
				value: Box::new(value),
			},
			tir::ExprKind::FieldAccess {
				object,
				field: member,
			} => {
				let (struct_index, args) = self.instantiate_struct(object.ty);
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let decl_index = usize::from(
					self.tir.items.structs[usize::from(struct_index)].lookup
						[&member.inner],
				);
				let phys_index =
					self.aggregate(aggregate_index).physical(decl_index);
				let tir::ExprKind::Local {
					scope_index,
					local_index,
				} = &object.kind
				else {
					unreachable!(
						"ObjectAccess assignment: object must be Local after place/value split"
					)
				};
				ExprKind::AggregateSet {
					scope_index: ScopeIndex::new(u32::from(*scope_index)),
					local_index: LocalIndex::new(u32::from(*local_index)),
					value_index: phys_index,
					value: Box::new(value),
				}
			}
			_ => unreachable!(
				"assignment target must be Local/Global/FieldAccess"
			),
		}
	}

	/// Builds the `Call` to `method_id` a compound-assignment operator
	/// resolves to — `current_value`/`rhs` are its two arguments (mirrors
	/// `MethodCall`'s lowering), and the call's own MIR type is
	/// `current_value`'s type, since every operator trait method returns
	/// `Self`. Records the call-graph edge so the inlining pass considers
	/// this call a candidate exactly like an ordinary `MethodCall` would —
	/// primitive impls (`impl Add for i32`, `#[inline]`) only collapse back
	/// to a native op if this edge exists.
	fn build_compound_operator_call(
		&mut self,
		method_id: ast::DefId,
		current_value: Expression,
		rhs: Expression,
	) -> Expression {
		self.record_call_edge(method_id);
		let ty = current_value.ty;
		let tir_idx = self.tir.items.expect_function_index(method_id);
		let callee_sig_idx = self.intern_tir_function_type(
			self.tir.items.functions[usize::from(tir_idx)].signature_index,
		);
		Expression {
			kind: ExprKind::Call {
				callee: Box::new(Expression {
					kind: ExprKind::Function { id: method_id },
					ty: ValueType::Function {
						signature_index: callee_sig_idx,
					},
				}),
				arguments: Box::new([current_value, rhs]),
			},
			ty,
		}
	}

	/// Resolves `GenericCompoundAssign`/`GenericCompoundStore`'s abstract
	/// trait method to a concrete one now that `self_type` is guaranteed
	/// concrete (the surrounding function has already been monomorphized for
	/// this instantiation). Compound operators have only the inherited `Self`
	/// argument, so they can use the same trait-function resolver as calls.
	pub(in crate::mir) fn resolve_generic_compound_method(
		&mut self,
		abstract_method_id: ast::DefId,
		self_type: tir::TypeIndex,
	) -> ast::DefId {
		let concrete_self = self
			.types
			.instantiate_type(self_type, self.current_type_env);
		let function_index =
			self.tir.items.expect_function_index(abstract_method_id);
		self.resolve_generic_function(function_index, Box::new([concrete_self]))
	}

	/// `CompoundAssign`/`GenericCompoundAssign` (target is `Local`/`Global`/
	/// `FieldAccess`): read the current value, call the resolved operator
	/// method, write the result back — `target`'s indices are safe to
	/// reference twice (`Copy` metadata, not a computation), so no
	/// once-only-lowering concern here, unlike `lower_compound_store`.
	pub(in crate::mir) fn lower_compound_assign(
		&mut self,
		func_ctx: &mut FunctionContext,
		target: &tir::Expression,
		rhs: &tir::Expression,
		method_id: ast::DefId,
		sink: &mut Vec<Expression>,
	) -> Expression {
		let current_value = self.lower_expression(func_ctx, target, sink);
		let lowered_rhs = self.lower_expression(func_ctx, rhs, sink);
		let call = self.build_compound_operator_call(
			method_id,
			current_value,
			lowered_rhs,
		);
		Expression {
			kind: self.lower_assign_target(target, call),
			ty: ValueType::Unit,
		}
	}

	/// `CompoundStore`/`GenericCompoundStore` (target is a `Place`): the
	/// careful one. Computes `target`'s address exactly once and sinks it
	/// into a temp local, reused via `LocalGet` for both the old-value read
	/// and the final store — fixes the pre-existing double-evaluation bug
	/// where e.g. `arr[i()] += 1` called `i()` twice (once per
	/// `lower_place_address` call). Mirrors the temp-local idiom already
	/// used elsewhere in this file (e.g. `lower_intrinsic`'s `slice_len`/
	/// `slice_ptr` arms).
	pub(in crate::mir) fn lower_compound_store(
		&mut self,
		func_ctx: &mut FunctionContext,
		target: &tir::Place,
		rhs: &tir::Expression,
		method_id: ast::DefId,
		sink: &mut Vec<Expression>,
	) -> Expression {
		let (ptr, offset, memory) =
			self.lower_place_address(func_ctx, target, sink);
		let ptr_ty = ptr.ty;
		let temp_idx = LocalIndex::new(func_ctx.frame[0].locals.len() as u32);
		func_ctx.frame[0].locals.push(Local {
			ty: ptr_ty,
			mutability: Mutability::Immutable,
		});
		sink.push(Expression {
			kind: ExprKind::LocalSet {
				scope_index: ScopeIndex::new(0),
				local_index: temp_idx,
				value: Box::new(ptr),
			},
			ty: ValueType::Unit,
		});

		let current_value = Expression {
			kind: ExprKind::PointerLoad {
				pointer: Box::new(Expression {
					kind: ExprKind::LocalGet {
						scope_index: ScopeIndex::new(0),
						local_index: temp_idx,
					},
					ty: ptr_ty,
				}),
				offset,
				memory,
			},
			ty: self.lower_type_index(target.ty),
		};
		let lowered_rhs = self.lower_expression(func_ctx, rhs, sink);
		let call = self.build_compound_operator_call(
			method_id,
			current_value,
			lowered_rhs,
		);
		Expression {
			kind: ExprKind::PointerStore {
				pointer: Box::new(Expression {
					kind: ExprKind::LocalGet {
						scope_index: ScopeIndex::new(0),
						local_index: temp_idx,
					},
					ty: ptr_ty,
				}),
				value: Box::new(call),
				offset,
				memory,
			},
			ty: ValueType::Unit,
		}
	}
}
