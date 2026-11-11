//! REFERENCE ONLY — not compiled, not declared as a module.
//!
//! The pre-transition MIR lowering pass (`impl MIR { fn build ... }` plus the
//! `Builder` that implemented it), extracted verbatim from `mir/mod.rs` when
//! MIR identities moved from `ast::DefId` to backend IDs. It targets the old
//! `tir::TIR` API and will not compile against the current checker.
//!
//! Kept on disk as a reference for the new TIR-to-MIR lowerer: the expression
//! lowering, place/address arithmetic, aggregate encoding and intrinsic
//! handling are still the best description of what MIR expects from TIR.


struct Builder<'tir> {
	tir: &'tir tir::TIR,
	interner: &'tir ast::StringInterner,
	types: TypeContext<'tir>,
	aggregates: AggregateInterner,
	signatures: SignatureInterner,
	/// Owner-scoped concrete substitutions for the function currently being
	/// lowered. All instantiated types live in `types`, never in TIR's pool.
	current_type_env: Option<TypeEnvId>,
	mono_registry: MonoRegistry,
	/// MIR id of the function currently being lowered. Set by `MIR::build`
	/// before each `lower_function` call (TIR id in Phase 1, synthetic mono id
	/// in Phase 2) so that call edges are recorded with accurate MIR ids.
	current_function_id: Option<ast::DefId>,
	/// Direct call edges collected during lowering: (caller_mir_id,
	/// callee_mir_id). Used after all functions are built to derive each
	/// function's `callers` list from actual MIR-level calls rather than
	/// TIR accesses.
	call_edges: Vec<(ast::DefId, ast::DefId)>,
	static_data: StaticDataPool,
}

struct FunctionContext {
	scopes: Vec<BlockScope>,
	/// Every local the function owns, in one flat, function-wide space.
	/// Mirrors `Function::locals` — this is where it's actually built up.
	locals: Vec<Local>,
	/// Flat offset where each scope's own locals begin in `locals` —
	/// transient, build-local scratch used only to translate TIR's
	/// `(scope_index, local_index)` pairs into flat MIR indices while
	/// lowering. Built once, up front, in `lower_function`; never persisted
	/// on `Function`/`BlockScope`.
	scope_offsets: Vec<u32>,
	current_scope_index: ScopeIndex,
	/// Static pool indices referenced by expressions in this function.
	static_data: Vec<u32>,
}

impl FunctionContext {
	/// Translates a TIR-level `(scope_index, local_index)` pair into this
	/// function's flat MIR `LocalIndex`.
	fn flat_local(
		&self,
		scope_index: tir::ScopeIndex,
		local_index: tir::LocalIndex,
	) -> LocalIndex {
		LocalIndex::new(
			self.scope_offsets[usize::from(scope_index)]
				+ u32::from(local_index),
		)
	}

	/// Appends a new function-wide temporary local and returns its flat
	/// index — the sink for every MIR-synthesized spill (bounds-check
	/// temporaries, non-local object bases, etc.). Replaces the old
	/// "scope 0" idiom: these temporaries no longer need a fictional home
	/// scope, since locals are addressed flatly regardless of where they
	/// live.
	fn push_temp_local(&mut self, ty: ValueType) -> LocalIndex {
		let index = LocalIndex::new(self.locals.len() as u32);
		self.locals.push(Local {
			ty,
			mutability: Mutability::Immutable,
		});
		index
	}
}

impl<'tir> Builder<'tir> {
	/// The aggregate `index` refers to, in the table built so far.
	#[inline]
	fn aggregate(&self, index: AggregateIndex) -> &Aggregate {
		self.aggregates.get(index)
	}

	fn resolve_memory_id(&mut self, memory_ty: tir::TypeIndex) -> ast::DefId {
		let concrete = self
			.types
			.instantiate_type(memory_ty, self.current_type_env);
		match self.types.get(concrete) {
			ConcreteType::Memory { id } => *id,
			_ => unreachable!(
				"memory type does not instantiate to ConcreteType::Memory"
			),
		}
	}

	/// The MIR pointer type for a memory, with the memory's width baked in
	/// so later stages can pick value types and access widths from the type
	/// alone, without a memory-table lookup.
	fn pointer_type(&self, memory: ast::DefId) -> ValueType {
		let tir_idx = usize::from(self.tir.items.expect_memory_index(memory));
		ValueType::Pointer {
			memory,
			kind: MemoryKind::from_type_index(
				self.tir.items.memories[tir_idx].size.inner,
			),
		}
	}

	/// Compute the memory layout of a type.
	pub fn compute_layout(&mut self, idx: tir::TypeIndex) -> Layout {
		let concrete = self.types.instantiate_type(idx, self.current_type_env);
		self.compute_type_layout(concrete)
	}

	fn compute_type_layout(&mut self, concrete: TypeId) -> Layout {
		let ty = self.lower_type(concrete);
		self.mir_type_layout(ty)
	}

	fn ensure_aggregate(
		&mut self,
		mir_fields: Box<[ValueType]>,
		order: FieldOrder,
	) -> AggregateIndex {
		self.aggregates.intern(mir_fields, order)
	}

	fn mir_type_layout(&self, ty: ValueType) -> Layout {
		self.aggregates.type_layout(ty)
	}

	fn instantiate_struct(
		&mut self,
		type_index: tir::TypeIndex,
	) -> (tir::StructIndex, Box<[TypeId]>) {
		let ty = self
			.types
			.instantiate_type(type_index, self.current_type_env);
		let ConcreteType::Struct { struct_index, args } = self.types.get(ty)
		else {
			unreachable!("expected a concrete struct type")
		};
		(*struct_index, args.clone())
	}

	/// Ensures an aggregate exists for a fully-instantiated struct.
	fn ensure_aggregate_for_struct(
		&mut self,
		struct_index: tir::StructIndex,
		args: &[TypeId],
	) -> AggregateIndex {
		// TODO: detect infinite-size cycles caused by generic struct instantiation
		// (e.g. `struct Node { inner: DirectIdentity<Node> }` where
		// `DirectIdentity<T> { value: T }`). TIR only catches concrete cycles;
		// generic ones require substitution, which only happens here during
		// monomorphization. When this is implemented, extend the DFS in
		// `tir::Builder::find_direct_struct_recursion` with a substitution map
		// and promote the error to TIR. For now, this will stack-overflow on
		// truly recursive generic instantiations.

		let tir_struct = &self.tir.items.structs[usize::from(struct_index)];
		let env = self.types.push_struct_env(tir_struct, args);
		let order = if tir_struct
			.attributes
			.contains(&tir::ItemAttribute::FixedOrder)
		{
			FieldOrder::Fixed
		} else {
			FieldOrder::Sorted
		};
		let mir_fields: Box<[ValueType]> = match &tir_struct.fields {
			tir::StructKind::Record { fields, .. } => fields
				.iter()
				.map(|field| self.lower_type_index_in(field.ty.inner, env))
				.collect(),
			tir::StructKind::Tuple { fields } => fields
				.iter()
				.map(|field| self.lower_type_index_in(field.ty.inner, env))
				.collect(),
		};
		self.ensure_aggregate(mir_fields, order)
	}

	fn lower_type_index(&mut self, type_idx: tir::TypeIndex) -> ValueType {
		self.lower_type_index_in(type_idx, self.current_type_env)
	}

	fn lower_type_index_in(
		&mut self,
		type_idx: tir::TypeIndex,
		env: Option<TypeEnvId>,
	) -> ValueType {
		let concrete = self.types.instantiate_type(type_idx, env);
		self.lower_type(concrete)
	}

	fn lower_type(&mut self, type_id: TypeId) -> ValueType {
		match self.types.get(type_id) {
			ConcreteType::Unit => ValueType::Unit,
			ConcreteType::Never => ValueType::Never,
			ConcreteType::U8 => ValueType::U8,
			ConcreteType::I8 => ValueType::I8,
			ConcreteType::U16 => ValueType::U16,
			ConcreteType::I16 => ValueType::I16,
			ConcreteType::U32 | ConcreteType::Char => ValueType::U32,
			ConcreteType::I32 => ValueType::I32,
			ConcreteType::U64 => ValueType::U64,
			ConcreteType::I64 => ValueType::I64,
			ConcreteType::F32 => ValueType::F32,
			ConcreteType::F64 => ValueType::F64,
			ConcreteType::Bool => ValueType::Bool,
			ConcreteType::Pointer { memory, .. }
			| ConcreteType::Array { memory, .. } => {
				let memory = *memory;
				let ConcreteType::Memory { id } = self.types.get(memory) else {
					unreachable!("pointer memory is not a concrete memory type")
				};
				self.pointer_type(*id)
			}
			ConcreteType::Slice { memory, .. } => {
				let memory = *memory;
				let ConcreteType::Memory { id } = self.types.get(memory) else {
					unreachable!("slice memory is not a concrete memory type")
				};
				let memory = *id;
				let tir_idx =
					usize::from(self.tir.items.expect_memory_index(memory));
				let kind_ty = self.tir.items.memories[tir_idx].size;
				let len_ty = self.lower_type_index_in(kind_ty.inner, None);
				// Slice layout is a fixed `{ ptr, len }` ABI contract, not a
				// sorting outcome — see the pipeline notes on slice lowering.
				let aggregate_index = self.ensure_aggregate(
					Box::new([self.pointer_type(memory), len_ty]),
					FieldOrder::Fixed,
				);
				ValueType::Aggregate { aggregate_index }
			}
			ConcreteType::Memory { .. } => ValueType::Unit,
			ConcreteType::Struct { struct_index, args } => {
				let struct_index = *struct_index;
				let args = args.clone();
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				ValueType::Aggregate { aggregate_index }
			}
			ConcreteType::Tuple { elements } => {
				let elements = elements.clone();
				let mir_elems =
					elements.iter().map(|&e| self.lower_type(e)).collect();
				let aggregate_index =
					self.ensure_aggregate(mir_elems, FieldOrder::Sorted);
				ValueType::Aggregate { aggregate_index }
			}
			ConcreteType::Enum { enum_index } => {
				let repr_ty =
					self.tir.items.enums[usize::from(*enum_index)].repr_type;
				self.lower_type_index_in(repr_ty, None)
			}
			ConcreteType::Function { params, result } => {
				let params = params.clone();
				let result = *result;
				let items = params
					.iter()
					.copied()
					.chain(std::iter::once(result))
					.map(|ty| self.lower_type(ty))
					.collect();
				let signature_index =
					self.intern_signature(FunctionSignature {
						items,
						params_count: params.len(),
					});
				ValueType::Function { signature_index }
			}
			ConcreteType::FunctionItem { id, type_args } => {
				let id = *id;
				let type_args = type_args.clone();
				let index = self.tir.items.expect_function_index(id);
				let function = &self.tir.items.functions[usize::from(index)];
				let env = self.types.push_function_env(function, &type_args);
				self.lower_type_index_in(function.signature_index, env)
			}
		}
	}

	fn intern_signature(&mut self, sig: FunctionSignature) -> SignatureIndex {
		self.signatures.intern(sig)
	}

	/// Converts a TIR function type (by its type-pool index) to a MIR
	/// `SignatureIndex`, interning the concrete signature on first use.
	fn intern_tir_function_type(
		&mut self,
		type_idx: tir::TypeIndex,
	) -> SignatureIndex {
		let ValueType::Function { signature_index } =
			self.lower_type_index(type_idx)
		else {
			unreachable!("expected function type")
		};
		signature_index
	}

	fn record_call_edge(&mut self, callee_id: ast::DefId) {
		if let Some(caller_id) = self.current_function_id {
			self.call_edges.push((caller_id, callee_id));
		}
	}

	/// Resolves a generic function or method after all of its type arguments
	/// have been instantiated. Trait declarations are redirected to the
	/// concrete impl member; a trait default is used only when no override is
	/// present.
	fn resolve_generic_function(
		&mut self,
		function_index: tir::FunctionIndex,
		resolved: Box<[TypeId]>,
	) -> ast::DefId {
		let function = &self.tir.items.functions[usize::from(function_index)];
		let id = function.id;
		let name = function.name.inner;
		let Some(tir::ItemParent::Trait(trait_index)) = function.parent else {
			return self.mono_registry.get_or_insert(id, resolved);
		};

		let concrete_self = resolved[0];
		let (impl_index, impl_args) = self
			.types
			.find_trait_impl(concrete_self, trait_index)
			.expect("no impl found for concrete trait function dispatch");
		match self
			.types
			.trait_member(impl_index, name)
			.expect("validated trait impl has no callable member")
		{
			TraitMember::Impl(
				tir::ImplEntry::Method(index)
				| tir::ImplEntry::AssocFunction(index),
			) => {
				let function = &self.tir.items.functions[usize::from(index)];
				let type_args: Box<[TypeId]> = impl_args
					.iter()
					.copied()
					.chain(resolved[1..].iter().copied())
					.collect();
				if type_args.is_empty() {
					function.id
				} else {
					self.mono_registry.get_or_insert(function.id, type_args)
				}
			}
			TraitMember::Default(
				tir::ImplEntry::Method(index)
				| tir::ImplEntry::AssocFunction(index),
			) => {
				let function = &self.tir.items.functions[usize::from(index)];
				self.mono_registry.get_or_insert(function.id, resolved)
			}
			_ => {
				unreachable!("trait function dispatch selected a non-function")
			}
		}
	}

	/// Whether `id` refers to an `#[intrinsic]` function. Intrinsic calls are
	/// eliminated entirely during lowering (substituted for a dedicated
	/// `ExprKind` variant) and never become a real `mir::Function`, so they
	/// must never be recorded as a call-graph edge — an intrinsic id showing
	/// up as someone's callee would leave `CallGraph`'s `callers` map without
	/// an entry for it (populated only from `mir.functions`), which the
	/// inlining pass's Kahn-queue loop assumes always exists.
	fn is_intrinsic(&self, id: ast::DefId) -> bool {
		let func_index = self.tir.items.expect_function_index(id);
		self.tir.items.functions[usize::from(func_index)]
			.attributes
			.contains(&tir::ItemAttribute::Intrinsic)
	}

	fn lower_function(&mut self, func: &tir::Function) -> Function {
		let body_idx = func
			.body
			.expect("lower_function called on bodyless function");
		let body = &self.tir.items.bodies[usize::from(body_idx)];

		let mut locals = Vec::new();
		let mut scope_offsets = Vec::with_capacity(body.stack.scopes.len());
		let scopes = body
			.stack
			.scopes
			.iter()
			.map(|scope| {
				let result_type_idx =
					scope.inferred_type.infer_or(tir::TypeIndex::UNIT);
				scope_offsets.push(locals.len() as u32);
				locals.extend(scope.locals.iter().map(|tir_local| Local {
					ty: self.lower_type_index(tir_local.ty),
					mutability: if tir_local.mut_span.is_some() {
						Mutability::Mutable
					} else {
						Mutability::Immutable
					},
				}));
				BlockScope {
					kind: scope.kind,
					result: self.lower_type_index(result_type_idx),
				}
			})
			.collect();

		let mut ctx = FunctionContext {
			current_scope_index: ScopeIndex::new(0),
			scopes,
			scope_offsets,
			locals,
			static_data: Vec::new(),
		};

		let mut top_sink = Vec::new();
		let block = self.lower_expression(&mut ctx, &body.block, &mut top_sink);

		Function {
			id: func.id,
			signature_index: self
				.intern_tir_function_type(func.signature_index),
			scopes: ctx.scopes,
			locals: ctx.locals,
			block,
			static_data: ctx.static_data,
		}
	}

	fn lower_global(&mut self, global: &tir::Global) -> Global {
		let ty = self.lower_type_index(global.ty.inner);
		let zero = match ty {
			ValueType::F32 | ValueType::F64 => ConstInit::Float(0.0),
			_ => ConstInit::Int(0),
		};
		let const_init = match global.value {
			Some(body_idx) => {
				match self.tir.items.bodies[usize::from(body_idx)].block.kind {
					tir::ExprKind::Int { value } => {
						ConstInit::Int(value as i64)
					}
					tir::ExprKind::Float { value } => ConstInit::Float(value),
					_ => zero,
				}
			}
			None => zero,
		};
		Global {
			id: global.id,
			ty,
			mutability: if global.mut_span.is_some() {
				Mutability::Mutable
			} else {
				Mutability::Immutable
			},
			const_init,
		}
	}

	/// Builds the synthetic `__wx_start` function that initializes all user
	/// globals in declaration order. Returns `None` when there are no globals
	/// with initializers.
	fn build_start_function(
		&mut self,
		tir: &tir::TIR,
		start_id: ast::DefId,
	) -> Option<Function> {
		let globals_with_init: Vec<&tir::Global> = tir
			.items
			.globals
			.iter()
			.filter(|g| {
				g.mut_span.is_some()
					&& g.value.is_some_and(|body_idx| {
						!matches!(
							tir.items.bodies[usize::from(body_idx)].block.kind,
							tir::ExprKind::Int { .. }
								| tir::ExprKind::Float { .. }
						)
					})
			})
			.collect();

		if globals_with_init.is_empty() {
			return None;
		}

		self.current_function_id = Some(start_id);

		// Root scope for the start function body (no params, no locals).
		let root_scope = BlockScope {
			kind: tir::BlockKind::Block,
			result: ValueType::Unit,
		};
		let mut combined_scopes: Vec<BlockScope> = vec![root_scope];
		let mut combined_locals: Vec<Local> = Vec::new();
		let mut combined_body: Vec<Expression> = Vec::new();
		let mut combined_static_data: Vec<u32> = Vec::new();

		for g in globals_with_init {
			let body = &tir.items.bodies[usize::from(g.value.unwrap())];

			let mut locals = Vec::new();
			let mut scope_offsets = Vec::with_capacity(body.stack.scopes.len());
			let scopes: Vec<BlockScope> = body
				.stack
				.scopes
				.iter()
				.map(|scope| {
					let result_ty =
						scope.inferred_type.infer_or(tir::TypeIndex::UNIT);
					scope_offsets.push(locals.len() as u32);
					locals.extend(scope.locals.iter().map(|tir_local| Local {
						ty: self.lower_type_index(tir_local.ty),
						mutability: if tir_local.mut_span.is_some() {
							Mutability::Mutable
						} else {
							Mutability::Immutable
						},
					}));
					BlockScope {
						kind: scope.kind,
						result: self.lower_type_index(result_ty),
					}
				})
				.collect();

			let mut ctx = FunctionContext {
				current_scope_index: ScopeIndex::new(0),
				scopes,
				scope_offsets,
				locals,
				static_data: Vec::new(),
			};

			let mut sink = Vec::new();
			let mut lowered =
				self.lower_expression(&mut ctx, &body.block, &mut sink);

			// Offset all scope indices and local indices so this global's
			// scopes/locals don't collide with prior globals' in the
			// combined pool.
			let scope_offset = ScopeIndex::new(combined_scopes.len() as u32);
			let local_offset = LocalIndex::new(combined_locals.len() as u32);
			rebase_scope(
				&mut lowered,
				scope_offset,
				ScopeIndex::new(0),
				local_offset,
			);
			for e in sink.iter_mut() {
				rebase_scope(e, scope_offset, ScopeIndex::new(0), local_offset);
			}

			combined_scopes.extend(ctx.scopes);
			combined_locals.extend(ctx.locals);

			combined_body.extend(sink);
			combined_body.push(Expression {
				kind: ExprKind::GlobalSet {
					id: g.id,
					value: Box::new(lowered),
				},
				ty: ValueType::Unit,
			});
			combined_static_data.extend(ctx.static_data);
		}

		let unit_sig = FunctionSignature {
			items: Box::new([ValueType::Unit]),
			params_count: 0,
		};
		let signature_index = self.intern_signature(unit_sig);

		Some(Function {
			id: start_id,
			signature_index,
			scopes: combined_scopes,
			locals: combined_locals,
			block: Expression {
				kind: ExprKind::Block {
					scope_index: ScopeIndex::new(0),
					expressions: combined_body.into_boxed_slice(),
				},
				ty: ValueType::Unit,
			},
			static_data: combined_static_data,
		})
	}

	/// Encode one compile-time element (Int or Float ExprKind + its MIR type)
	/// as little-endian bytes appended to `buf`.
	fn encode_element(buf: &mut Vec<u8>, kind: &tir::ExprKind, ty: ValueType) {
		match kind {
			tir::ExprKind::Int { value } => match ty {
				ValueType::I8 | ValueType::U8 => buf.push(*value as u8),
				ValueType::I16 | ValueType::U16 => {
					buf.extend_from_slice(&(*value as u16).to_le_bytes())
				}
				ValueType::I32 | ValueType::U32 => {
					buf.extend_from_slice(&(*value as u32).to_le_bytes())
				}
				ValueType::I64 | ValueType::U64 => {
					buf.extend_from_slice(&value.to_le_bytes())
				}
				// An integer literal pinned to a float member of a typeset by
				// monomorphization (TIR verified it is exactly representable).
				ValueType::F32 => buf.extend_from_slice(
					&(*value as f32).to_bits().to_le_bytes(),
				),
				ValueType::F64 => buf.extend_from_slice(
					&(*value as f64).to_bits().to_le_bytes(),
				),
				_ => unreachable!(),
			},
			tir::ExprKind::Float { value } => match ty {
				ValueType::F32 => buf.extend_from_slice(
					&(*value as f32).to_bits().to_le_bytes(),
				),
				ValueType::F64 => {
					buf.extend_from_slice(&value.to_bits().to_le_bytes())
				}
				_ => unreachable!(),
			},
			_ => unreachable!(),
		}
	}

	/// Add a static data entry (array constant); returns `(index, byte_size)`.
	fn push_static_data(
		&mut self,
		func_ctx: &mut FunctionContext,
		bytes: Vec<u8>,
		align: u32,
		memory: ast::DefId,
	) -> (u32, u32) {
		let (index, size) = self.static_data.push(bytes, align, memory);
		func_ctx.static_data.push(index);
		(index, size)
	}

	/// Add a string literal entry, deduplicating by (symbol, memory);
	/// returns `(index, byte_size)`.
	fn push_string_data(
		&mut self,
		func_ctx: &mut FunctionContext,
		symbol: SymbolU32,
		memory: ast::DefId,
	) -> (u32, u32) {
		let s = self
			.interner
			.resolve(symbol)
			.expect("unresolved string symbol");
		let (index, size) =
			self.static_data.push_string(symbol, s.as_bytes(), memory);
		func_ctx.static_data.push(index);
		(index, size)
	}

	fn lower_index_address(
		&mut self,
		func_ctx: &mut FunctionContext,
		object: &tir::Expression,
		index: &tir::Expression,
		elem_ty: tir::TypeIndex,
		sink: &mut Vec<Expression>,
	) -> IndexAddress {
		let elem_size = self.compute_layout(elem_ty).size;
		let object_ty = self
			.types
			.instantiate_type(object.ty, self.current_type_env);
		let slice_memory = match self.types.get(object_ty) {
			ConcreteType::Slice { memory, .. } => Some(*memory),
			_ => None,
		};

		// For slices the lowered object is an aggregate {ptr, len}; extract
		// the pointer field (index 0) as the base address.
		let (base, ptr_ty) = if let Some(memory) = slice_memory {
			let ConcreteType::Memory { id: memory_id } = self.types.get(memory)
			else {
				unreachable!("slice memory is not a concrete memory type")
			};
			let memory_id = *memory_id;
			let ptr_ty = self.pointer_type(memory_id);
			let li = match &object.kind {
				tir::ExprKind::Local {
					scope_index,
					local_index,
				} => func_ctx.flat_local(*scope_index, *local_index),
				_ => {
					let lowered = self.lower_expression(func_ctx, object, sink);
					let obj_ty = self.lower_type_index(object.ty);
					let temp = func_ctx.push_temp_local(obj_ty);
					sink.push(Expression {
						kind: ExprKind::LocalSet {
							local_index: temp,
							value: Box::new(lowered),
						},
						ty: ValueType::Unit,
					});
					temp
				}
			};
			let ptr = Expression {
				kind: ExprKind::AggregateGet {
					local_index: li,
					value_index: PhysIndex::new(0),
				},
				ty: ptr_ty,
			};
			(ptr, ptr_ty)
		} else {
			let ptr_ty = self.lower_type_index(object.ty);
			let base = self.lower_expression(func_ctx, object, sink);
			(base, ptr_ty)
		};

		// Constant index: fold `value * elem_size` directly into the memarg immediate.
		if let tir::ExprKind::Int { value } = index.kind {
			return IndexAddress::Constant {
				ptr: base,
				byte_offset: (value as u32).wrapping_mul(elem_size),
			};
		}

		let idx_ty = self.lower_type_index(index.ty);
		let idx = self.lower_expression(func_ctx, index, sink);
		IndexAddress::Dynamic(Expression {
			kind: ExprKind::Add {
				left: Box::new(base),
				right: Box::new(Expression {
					kind: ExprKind::Mul {
						left: Box::new(idx),
						right: Box::new(Expression {
							kind: ExprKind::Int {
								value: elem_size as i64,
							},
							ty: idx_ty,
						}),
					},
					ty: idx_ty,
				}),
			},
			ty: ptr_ty,
		})
	}

	/// Lowers an already-folded compile-time constant value directly to a MIR
	/// scalar — shared by every place that reads a `ConstValue` cached on TIR
	/// (`Constant`, `EnumVariant`) so codegen never has to re-walk the original
	/// expression tree just to rediscover a value TIR already computed.
	fn lower_const_value(
		const_value: tir::ConstValue,
		ty: ValueType,
	) -> Expression {
		match const_value {
			tir::ConstValue::Int(value) => Expression {
				kind: ExprKind::Int { value },
				ty,
			},
			tir::ConstValue::Float(value) => Expression {
				kind: ExprKind::Float { value },
				ty,
			},
			tir::ConstValue::Bool(value) => Expression {
				kind: ExprKind::Bool { value },
				ty,
			},
			tir::ConstValue::Char(value) => Expression {
				kind: ExprKind::Int {
					value: value as i64,
				},
				ty,
			},
		}
	}

	/// Stores `value` into a fresh function-wide local and returns its flat
	/// index, so it can be read back more than once without re-evaluating
	/// it.
	///
	/// The temp-local idiom used throughout this file: `AggregateGet` and
	/// friends address a local, never an arbitrary expression, so anything
	/// they need to read has to be parked in one first. Locals are flat and
	/// function-wide (`Function::locals`), so a temp just gets appended
	/// directly — there's no "home scope" to route it through.
	fn spill_to_temp(
		&mut self,
		func_ctx: &mut FunctionContext,
		value: Expression,
		sink: &mut Vec<Expression>,
	) -> LocalIndex {
		let local_index = func_ctx.push_temp_local(value.ty);
		sink.push(Expression {
			kind: ExprKind::LocalSet {
				local_index,
				value: Box::new(value),
			},
			ty: ValueType::Unit,
		});
		local_index
	}

	fn lower_expression(
		&mut self,
		func_ctx: &mut FunctionContext,
		expr: &tir::Expression,
		sink: &mut Vec<Expression>,
	) -> Expression {
		use crate::ast::UnaryOp;

		match &expr.kind {
			tir::ExprKind::Error
			| tir::ExprKind::Placeholder
			| tir::ExprKind::Memory { .. } => Expression {
				kind: ExprKind::Noop,
				ty: ValueType::Unit,
			},
			tir::ExprKind::Unreachable => Expression {
				kind: ExprKind::Unreachable,
				ty: ValueType::Never,
			},
			tir::ExprKind::Int { value } => {
				// An integer literal bounded by a float-containing typeset keeps
				// its `Int` node through TIR; once monomorphization pins the
				// type to a float, it becomes a float constant. TIR already
				// checked the value is exactly representable.
				let ty = self.lower_type_index(expr.ty);
				match ty {
					ValueType::F32 | ValueType::F64 => Expression {
						kind: ExprKind::Float {
							value: *value as f64,
						},
						ty,
					},
					_ => Expression {
						kind: ExprKind::Int {
							value: *value as i64,
						},
						ty,
					},
				}
			}
			tir::ExprKind::Float { value } => Expression {
				kind: ExprKind::Float { value: *value },
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Bool { value } => Expression {
				kind: ExprKind::Bool { value: *value },
				ty: ValueType::Bool,
			},
			tir::ExprKind::Global { id } => Expression {
				kind: ExprKind::Global { id: *id },
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Local {
				scope_index,
				local_index,
			} => Expression {
				kind: ExprKind::LocalGet {
					local_index: func_ctx
						.flat_local(*scope_index, *local_index),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Function { id } => {
				let concrete =
					self.types.instantiate_type(expr.ty, self.current_type_env);
				let generic = match self.types.get(concrete) {
					ConcreteType::FunctionItem { id, type_args }
						if !type_args.is_empty() =>
					{
						Some((*id, type_args.clone()))
					}
					_ => None,
				};
				match generic {
					Some((fn_id, concrete_args)) => {
						let function_index =
							self.tir.items.expect_function_index(fn_id);
						let mono_id = self.resolve_generic_function(
							function_index,
							concrete_args,
						);
						if !self.is_intrinsic(fn_id) {
							self.record_call_edge(mono_id);
						}
						let ValueType::Function { signature_index } =
							self.lower_type(concrete)
						else {
							unreachable!(
								"function item lowered to a non-function"
							)
						};
						Expression {
							kind: ExprKind::Function { id: mono_id },
							ty: ValueType::Function { signature_index },
						}
					}
					_ => {
						if !self.is_intrinsic(*id) {
							self.record_call_edge(*id);
						}
						Expression {
							kind: ExprKind::Function { id: *id },
							ty: self.lower_type(concrete),
						}
					}
				}
			}
			tir::ExprKind::Char { value } => Expression {
				kind: ExprKind::Int {
					value: *value as i64,
				},
				ty: ValueType::U32,
			},
			tir::ExprKind::String { symbol } => {
				// The literal's slice type says which memory its bytes are
				// placed in.
				let concrete =
					self.types.instantiate_type(expr.ty, self.current_type_env);
				let memory = match self.types.get(concrete) {
					ConcreteType::Slice { memory, .. } => *memory,
					_ => unreachable!("string literal must have slice type"),
				};
				let ConcreteType::Memory { id: memory_id } =
					self.types.get(memory)
				else {
					unreachable!("string literal memory is not concrete")
				};
				let memory_id = *memory_id;
				let (data_index, size) =
					self.push_string_data(func_ctx, *symbol, memory_id);
				let ty = self.lower_type_index(expr.ty);
				let mem_idx =
					usize::from(self.tir.items.expect_memory_index(memory_id));
				Expression {
					kind: ExprKind::Aggregate {
						values: Box::new([
							Expression {
								kind: ExprKind::StaticPointer { data_index },
								ty: self.pointer_type(memory_id),
							},
							Expression {
								kind: ExprKind::Int { value: size as i64 },
								// Slice len has the memory's size type
								// (u64 for a 64-bit memory).
								ty: self.lower_type_index(
									self.tir.items.memories[mem_idx].size.inner,
								),
							},
						]),
					},
					ty,
				}
			}
			tir::ExprKind::Return { value } => Expression {
				kind: ExprKind::Return {
					value: value.as_ref().map(|v| {
						Box::new(self.lower_expression(func_ctx, v, sink))
					}),
				},
				ty: ValueType::Never,
			},
			tir::ExprKind::EnumVariant {
				enum_index,
				variant_index,
			} => {
				let enum_ = &self.tir.items.enums[usize::from(*enum_index)];
				let variant = &enum_.variants[usize::from(*variant_index)];
				match variant.const_value {
					Some(const_value) => Self::lower_const_value(
						const_value,
						self.lower_type_index(expr.ty),
					),
					// Error-free TIR guarantees every variant folds to a
					// constant — see the `NotConstEvaluatable`/range checks
					// in `Builder::build_enum`. MIR::build assumes TIR has
					// no errors (the CLI aborts beforehand otherwise).
					None => unreachable!(
						"enum variant without a folded compile-time value"
					),
				}
			}
			tir::ExprKind::GenericCall {
				id,
				type_args,
				arguments,
			} => {
				let func_index = self.tir.items.expect_function_index(*id);
				let func = &self.tir.items.functions[usize::from(func_index)];
				if func.attributes.iter().any(|attr| match attr {
					tir::ItemAttribute::Intrinsic => true,
					_ => false,
				}) {
					return self.lower_intrinsic(
						func_ctx,
						func.name.inner,
						expr.ty,
						type_args,
						arguments,
						sink,
					);
				}

				let concrete_type_args = self
					.types
					.instantiate_types(type_args, self.current_type_env);
				let callee_env =
					self.types.push_function_env(func, &concrete_type_args);
				let ValueType::Function {
					signature_index: callee_sig_idx,
				} = self.lower_type_index_in(func.signature_index, callee_env)
				else {
					unreachable!("function signature lowered to a non-function")
				};
				let mono_id = self
					.resolve_generic_function(func_index, concrete_type_args);
				self.record_call_edge(mono_id);

				let lowered_args: Box<[_]> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call {
						callee: Box::new(Expression {
							kind: ExprKind::Function { id: mono_id },
							ty: ValueType::Function {
								signature_index: callee_sig_idx,
							},
						}),
						arguments: lowered_args,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::GenericMethodCall {
				id,
				type_args,
				arguments,
			} => {
				let tir_idx = self.tir.items.expect_function_index(*id);
				let tir_func = &self.tir.items.functions[usize::from(tir_idx)];
				let resolved = self
					.types
					.instantiate_types(type_args, self.current_type_env);
				let callee_env =
					self.types.push_function_env(tir_func, &resolved);
				let ValueType::Function {
					signature_index: callee_sig_idx,
				} = self.lower_type_index_in(tir_func.signature_index, callee_env)
				else {
					unreachable!("method signature lowered to a non-function")
				};

				let target_id =
					self.resolve_generic_function(tir_idx, resolved);
				self.record_call_edge(target_id);

				let lowered_args: Box<[_]> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call {
						callee: Box::new(Expression {
							kind: ExprKind::Function { id: target_id },
							ty: ValueType::Function {
								signature_index: callee_sig_idx,
							},
						}),
						arguments: lowered_args,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Call { callee, arguments } => {
				let callee =
					Box::new(self.lower_expression(func_ctx, callee, sink));
				if let ExprKind::Function { id } = callee.kind {
					let func_index = self.tir.items.expect_function_index(id);
					let func =
						&self.tir.items.functions[usize::from(func_index)];
					if func.attributes.iter().any(|attr| match attr {
						tir::ItemAttribute::Intrinsic => true,
						_ => false,
					}) {
						return self.lower_intrinsic(
							func_ctx,
							func.name.inner,
							expr.ty,
							&[],
							arguments,
							sink,
						);
					}
					self.record_call_edge(id);
				};
				let arguments = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call { callee, arguments },
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::MethodCall { arguments, id } => {
				self.record_call_edge(*id);
				let tir_idx = self.tir.items.expect_function_index(*id);
				let callee_sig_idx = self.intern_tir_function_type(
					self.tir.items.functions[usize::from(tir_idx)]
						.signature_index,
				);
				let callee = Box::new(Expression {
					kind: ExprKind::Function { id: *id },
					ty: ValueType::Function {
						signature_index: callee_sig_idx,
					},
				});
				let arguments: Box<_> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				Expression {
					kind: ExprKind::Call { callee, arguments },
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::AbstractConstAccess { receiver, id } => {
				// Always a trait's own declaration — see the variant's
				// doc comment: a const already resolved through a
				// concrete `impl Trait for Target` (or an inherent
				// impl, or a plain module-level const) never becomes
				// this node, only bare `ExprKind::Const`.
				let declared_index = self.tir.items.expect_const_index(*id);
				let declared =
					&self.tir.items.constants[usize::from(declared_index)];
				let Some(tir::ItemParent::Trait(trait_index)) = declared.parent
				else {
					unreachable!(
						"AbstractConstAccess always names a trait's own const declaration"
					)
				};
				let name = declared.name.inner;
				let receiver = self
					.types
					.instantiate_type(*receiver, self.current_type_env);
				let (impl_index, _) =
					self.types.find_trait_impl(receiver, trait_index).expect(
						"no impl found for concrete trait constant dispatch",
					);
				let const_index = match self
					.types
					.trait_member(impl_index, name)
					.expect("validated trait impl has no constant member")
				{
					TraitMember::Impl(tir::ImplEntry::AssocConstant(index))
					| TraitMember::Default(tir::ImplEntry::AssocConstant(
						index,
					)) => index,
					_ => unreachable!(
						"trait constant dispatch selected a non-constant"
					),
				};
				let const_idx = usize::from(const_index);
				let result_ty = self.lower_type_index(expr.ty);
				// Only `DATA_END`/`INDEX` are compiler-synthesized —
				// every other `Memory`-trait const (e.g. `PAGE_SIZE`)
				// is an ordinary default value, already folded to a
				// `const_value` in TIR, and falls through to the
				// generic path below like any other const.
				if let ConcreteType::Memory { id } = self.types.get(receiver) {
					let const_name_sym =
						self.tir.items.constants[const_idx].name.inner;
					let const_name =
						self.interner.resolve(const_name_sym).unwrap();
					match const_name {
						"DATA_END" => {
							return Expression {
								kind: ExprKind::MemoryOffset { memory: *id },
								ty: result_ty,
							};
						}
						"INDEX" => {
							return Expression {
								kind: ExprKind::MemoryIndex { memory: *id },
								ty: result_ty,
							};
						}
						_ => {}
					}
				};

				match self.tir.items.constants[const_idx].const_value {
					Some(const_value) => {
						Self::lower_const_value(const_value, result_ty)
					}
					None => unreachable!(),
				}
			}
			tir::ExprKind::Const { id } => {
				let const_idx =
					usize::from(self.tir.items.expect_const_index(*id));
				let result_ty = self.lower_type_index(expr.ty);
				if let Some(const_value) =
					self.tir.items.constants[const_idx].const_value
				{
					Self::lower_const_value(const_value, result_ty)
				} else if self.tir.items.constants[const_idx].value.is_some() {
					todo!("complex const expression in MIR lowering")
				} else {
					unreachable!(
						"compiler-implemented constant referenced outside namespace access"
					)
				}
			}
			tir::ExprKind::FieldAccess {
				object,
				field: member,
			} => {
				let (struct_index, args) = self.instantiate_struct(object.ty);
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let aggregate = self.aggregate(aggregate_index);
				let phys_index = aggregate.physical(usize::from(member.inner));
				let field_ty = aggregate.field(phys_index).ty;

				match &object.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => Expression {
						kind: ExprKind::AggregateGet {
							local_index: func_ctx
								.flat_local(*scope_index, *local_index),
							value_index: phys_index,
						},
						ty: field_ty,
					},
					_ => {
						let object_ty = self.lower_type_index(object.ty);
						let object_lowered =
							self.lower_expression(func_ctx, object, sink);

						let temp_idx = func_ctx.push_temp_local(object_ty);

						sink.push(Expression {
							kind: ExprKind::LocalSet {
								local_index: temp_idx,
								value: Box::new(object_lowered),
							},
							ty: ValueType::Unit,
						});

						Expression {
							kind: ExprKind::AggregateGet {
								local_index: temp_idx,
								value_index: phys_index,
							},
							ty: field_ty,
						}
					}
				}
			}
			tir::ExprKind::RecordStructInit { fields, .. } => {
				let (struct_index, args) = self.instantiate_struct(expr.ty);
				// `fields` is in source-written order, not declaration order
				// (see `tir::ExprKind::RecordStructInit`) — lower in that
				// order so side effects run as written, then use each
				// entry's own `FieldIndex` (not its position here) to place
				// it.
				let lowered: Vec<(tir::FieldIndex, Expression)> = fields
					.iter()
					.map(|(field_index, f)| {
						(*field_index, self.lower_expression(func_ctx, f, sink))
					})
					.collect();
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let aggregate = self.aggregate(aggregate_index);
				let mut phys_slots: Vec<Option<Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (decl, expr) in lowered {
					phys_slots
						[usize::from(aggregate.physical(usize::from(decl)))] = Some(expr);
				}
				let values: Box<[Expression]> =
					phys_slots.into_iter().map(|e| e.unwrap()).collect();
				Expression {
					kind: ExprKind::Aggregate { values },
					ty: ValueType::Aggregate { aggregate_index },
				}
			}
			tir::ExprKind::TupleStructInit { arguments, .. } => {
				let (struct_index, args) = self.instantiate_struct(expr.ty);
				// Lowered fully before `aggregate` borrows `self` below —
				// `lower_expression` needs `&mut self`. Position *is* the
				// declared field index here (no `FieldIndex` to read),
				// still lowered left to right, matching source order —
				// which for a tuple struct is always also declaration
				// order.
				let lowered: Vec<Expression> = arguments
					.iter()
					.map(|arg| self.lower_expression(func_ctx, arg, sink))
					.collect();
				let aggregate_index =
					self.ensure_aggregate_for_struct(struct_index, &args);
				let aggregate = self.aggregate(aggregate_index);
				let mut phys_slots: Vec<Option<Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (position, expr) in lowered.into_iter().enumerate() {
					phys_slots[usize::from(aggregate.physical(position))] =
						Some(expr);
				}
				let values: Box<[Expression]> =
					phys_slots.into_iter().map(|e| e.unwrap()).collect();
				Expression {
					kind: ExprKind::Aggregate { values },
					ty: ValueType::Aggregate { aggregate_index },
				}
			}
			tir::ExprKind::TupleInit { elements } => {
				let concrete =
					self.types.instantiate_type(expr.ty, self.current_type_env);
				let concrete_elements = match self.types.get(concrete) {
					ConcreteType::Tuple { elements } => elements.clone(),
					_ => unreachable!("TupleInit type must be Tuple"),
				};
				let types: Box<[ValueType]> = concrete_elements
					.iter()
					.copied()
					.map(|ty| self.lower_type(ty))
					.collect();
				let lowered: Vec<Expression> = elements
					.iter()
					.map(|expr| self.lower_expression(func_ctx, expr, sink))
					.collect();
				let aggregate_index =
					self.ensure_aggregate(types, FieldOrder::Sorted);
				let aggregate = self.aggregate(aggregate_index);
				let mut phys_slots: Vec<Option<Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (decl, expr) in lowered.into_iter().enumerate() {
					phys_slots[usize::from(aggregate.physical(decl))] =
						Some(expr);
				}
				let values: Box<[Expression]> =
					phys_slots.into_iter().map(|e| e.unwrap()).collect();
				Expression {
					kind: ExprKind::Aggregate { values },
					ty: ValueType::Aggregate { aggregate_index },
				}
			}
			tir::ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let condition =
					Box::new(self.lower_expression(func_ctx, condition, sink));
				let then_block =
					Box::new(self.lower_expression(func_ctx, then_block, sink));
				let else_block = else_block.as_ref().map(|e| {
					Box::new(self.lower_expression(func_ctx, e, sink))
				});
				Expression {
					kind: ExprKind::IfElse {
						condition,
						then_block,
						else_block,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Match { scrutinee, arms } => {
				let selector =
					Box::new(self.lower_expression(func_ctx, scrutinee, sink));
				let mut cases: Vec<(i64, Expression)> =
					Vec::with_capacity(arms.len());
				let mut default: Option<Box<Expression>> = None;
				for arm in arms.iter() {
					let body = self.lower_expression(func_ctx, &arm.body, sink);
					match arm.pattern {
						tir::Pattern::Wildcard => {
							default = Some(Box::new(body));
						}
						tir::Pattern::Int(v) => cases.push((v, body)),
						tir::Pattern::Bool(v) => cases.push((v as i64, body)),
						tir::Pattern::Char(v) => cases.push((v as i64, body)),
						tir::Pattern::EnumVariant {
							enum_index,
							variant_index,
						} => {
							let variant = &self.tir.items.enums
								[usize::from(enum_index)]
							.variants[usize::from(variant_index)];
							let discriminant = match variant.const_value {
								Some(tir::ConstValue::Int(v)) => v,
								// Error-free TIR guarantees an integer-repr
								// enum's variants fold to an int constant —
								// see the `EnumReprNotInteger` check in
								// `Builder::build_enum`.
								_ => unreachable!(
									"enum variant without a folded integer compile-time value"
								),
							};
							cases.push((discriminant, body));
						}
					}
				}
				Expression {
					kind: ExprKind::Switch {
						selector,
						cases: cases.into_boxed_slice(),
						default,
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Break { scope_index, value } => Expression {
				kind: ExprKind::Break {
					scope_index: ScopeIndex::new(u32::from(*scope_index)),
					value: value.as_ref().map(|v| {
						Box::new(self.lower_expression(func_ctx, v, sink))
					}),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Continue { scope_index } => Expression {
				kind: ExprKind::Continue {
					scope_index: ScopeIndex::new(u32::from(*scope_index)),
				},
				ty: ValueType::Never,
			},
			tir::ExprKind::Loop { scope_index, block } => Expression {
				kind: ExprKind::Loop {
					scope_index: ScopeIndex::new(u32::from(*scope_index)),
					block: Box::new(
						self.lower_expression(func_ctx, block, sink),
					),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::Block {
				scope_index,
				expressions,
				result,
			} => {
				func_ctx.current_scope_index =
					ScopeIndex::new(u32::from(*scope_index));

				let mut inner_sink: Vec<Expression> = Vec::new();
				for expr in expressions.iter().chain(result.as_deref()) {
					let lowered_expr =
						self.lower_expression(func_ctx, expr, &mut inner_sink);
					inner_sink.push(lowered_expr);
				}

				Expression {
					kind: ExprKind::Block {
						scope_index: ScopeIndex::new(u32::from(*scope_index)),
						expressions: inner_sink.into_boxed_slice(),
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::LocalDeclaration {
				scope_index,
				local_index,
				value,
				..
			} => Expression {
				kind: ExprKind::LocalSet {
					local_index: func_ctx
						.flat_local(*scope_index, *local_index),
					value: Box::new(
						self.lower_expression(func_ctx, value, sink),
					),
				},
				ty: self.lower_type_index(expr.ty),
			},
			tir::ExprKind::DestructureDeclaration { value, bindings } => {
				if bindings.is_empty() {
					// Nothing is bound — `local Point::{ .. } = p;` or a
					// pattern of nothing but `_`. All that remains is to run
					// the initializer for its effects.
					let value = self.lower_expression(func_ctx, value, sink);
					return Expression {
						kind: ExprKind::Drop {
							value: Box::new(value),
						},
						ty: ValueType::Unit,
					};
				}

				// Every binding reads out of one local, so the initializer is
				// evaluated exactly once. A value that already *is* a local
				// needs no copy.
				let scrutinee = match &value.kind {
					tir::ExprKind::Local {
						scope_index,
						local_index,
					} => func_ctx.flat_local(*scope_index, *local_index),
					_ => {
						let value =
							self.lower_expression(func_ctx, value, sink);
						self.spill_to_temp(func_ctx, value, sink)
					}
				};

				// Each store goes straight into `sink` as it is built, so the
				// intermediate spills a nested path needs stay next to the
				// binding that asked for them.
				let first_store = sink.len();
				for binding in bindings.iter() {
					let mut local_index = scrutinee;
					let mut projected: Option<Expression> = None;

					for step in binding.path.iter() {
						// `AggregateGet` reads a local, never an arbitrary
						// expression, so each intermediate hop of a nested
						// pattern has to land in one first.
						if let Some(value) = projected.take() {
							local_index =
								self.spill_to_temp(func_ctx, value, sink);
						}

						let ValueType::Aggregate { aggregate_index } =
							self.lower_type_index(step.aggregate_ty)
						else {
							unreachable!(
								"destructuring path step must name an aggregate"
							)
						};
						let aggregate = self.aggregate(aggregate_index);
						// Tuples are alignment-sorted just like structs, so
						// the declaration index has to be mapped through.
						let value_index =
							aggregate.physical(step.index as usize);
						let ty = aggregate.field(value_index).ty;

						projected = Some(Expression {
							kind: ExprKind::AggregateGet {
								local_index,
								value_index,
							},
							ty,
						});
					}

					let value = projected
						.expect("a destructured binding has at least one step");
					sink.push(Expression {
						kind: ExprKind::LocalSet {
							local_index: func_ctx.flat_local(
								binding.scope_index,
								binding.local_index,
							),
							value: Box::new(value),
						},
						ty: ValueType::Unit,
					});
				}

				// The statement's own value is the last store; everything
				// before it already sits in `sink` in order.
				debug_assert!(sink.len() > first_store);
				sink.pop().expect("bindings is non-empty")
			}
			tir::ExprKind::Unary { operator, operand } => {
				let operand =
					Box::new(self.lower_expression(func_ctx, operand, sink));
				Expression {
					kind: match operator.inner {
						UnaryOp::InvertSign => ExprKind::Neg { value: operand },
						UnaryOp::Not => ExprKind::Eqz { value: operand },
						UnaryOp::BitNot => ExprKind::BitNot { value: operand },
					},
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::Binary {
				operator,
				left,
				right,
			} => {
				use tir::BinaryOp;
				let left =
					Box::new(self.lower_expression(func_ctx, left, sink));
				let right =
					Box::new(self.lower_expression(func_ctx, right, sink));

				let kind = match operator.inner {
					BinaryOp::Add => ExprKind::Add { left, right },
					BinaryOp::Sub => ExprKind::Sub { left, right },
					BinaryOp::Mul => ExprKind::Mul { left, right },
					BinaryOp::Div => ExprKind::Div { left, right },
					BinaryOp::Rem => ExprKind::Rem { left, right },
					BinaryOp::Eq => ExprKind::Eq { left, right },
					BinaryOp::NotEq => ExprKind::NotEq { left, right },
					BinaryOp::Less => ExprKind::Less { left, right },
					BinaryOp::LessEq => ExprKind::LessEq { left, right },
					BinaryOp::Greater => ExprKind::Greater { left, right },
					BinaryOp::GreaterEq => ExprKind::GreaterEq { left, right },
					BinaryOp::And => ExprKind::And { left, right },
					BinaryOp::Or => ExprKind::Or { left, right },
					BinaryOp::BitAnd => ExprKind::BitAnd { left, right },
					BinaryOp::BitOr => ExprKind::BitOr { left, right },
					BinaryOp::BitXor => ExprKind::BitXor { left, right },
					BinaryOp::LeftShift => ExprKind::LeftShift { left, right },
					BinaryOp::RightShift => {
						ExprKind::RightShift { left, right }
					}
				};

				Expression {
					kind,
					ty: self.lower_type_index(expr.ty),
				}
			}
			tir::ExprKind::ArrayLiteral { elements, memory } => {
				let concrete =
					self.types.instantiate_type(expr.ty, self.current_type_env);
				let elem_ty = match self.types.get(concrete) {
					ConcreteType::Array { of, .. } => *of,
					_ => unreachable!(),
				};
				let memory_id = self.resolve_memory_id(*memory);
				let align = self.compute_type_layout(elem_ty).align;
				let elem_value_ty = self.lower_type(elem_ty);
				let mut bytes = Vec::new();
				for elem in elements.iter() {
					Self::encode_element(&mut bytes, &elem.kind, elem_value_ty);
				}
				if bytes.is_empty() {
					return Expression {
						kind: ExprKind::Int { value: 0 },
						ty: self.pointer_type(memory_id),
					};
				}
				let (data_index, _) =
					self.push_static_data(func_ctx, bytes, align, memory_id);
				Expression {
					kind: ExprKind::StaticPointer { data_index },
					ty: self.pointer_type(memory_id),
				}
			}
			tir::ExprKind::ArrayRepeat {
				value,
				count,
				memory,
			} => {
				let concrete =
					self.types.instantiate_type(expr.ty, self.current_type_env);
				let elem_ty = match self.types.get(concrete) {
					ConcreteType::Array { of, .. } => *of,
					_ => unreachable!(),
				};
				let memory_id = self.resolve_memory_id(*memory);
				let align = self.compute_type_layout(elem_ty).align;
				let elem_value_ty = self.lower_type(elem_ty);
				let mut elem_bytes = Vec::new();
				Self::encode_element(
					&mut elem_bytes,
					&value.kind,
					elem_value_ty,
				);
				let bytes = elem_bytes.repeat(*count as usize);
				if bytes.is_empty() {
					return Expression {
						kind: ExprKind::Int { value: 0 },
						ty: self.pointer_type(memory_id),
					};
				}
				let (data_index, _) =
					self.push_static_data(func_ctx, bytes, align, memory_id);
				Expression {
					kind: ExprKind::StaticPointer { data_index },
					ty: self.pointer_type(memory_id),
				}
			}
			tir::ExprKind::Load { place } => {
				let (ptr, offset, memory) =
					self.lower_place_address(func_ctx, place, sink);
				Expression {
					kind: ExprKind::PointerLoad {
						pointer: Box::new(ptr),
						offset,
						memory,
					},
					ty: self.lower_type_index(place.ty),
				}
			}
			tir::ExprKind::AddressOf { place, .. } => {
				let (ptr, offset, _memory) =
					self.lower_place_address(func_ctx, place, sink);
				let ptr_ty = self.lower_type_index(expr.ty);
				if offset == 0 {
					ptr
				} else {
					Expression {
						kind: ExprKind::Add {
							left: Box::new(ptr),
							right: Box::new(Expression {
								kind: ExprKind::Int {
									value: offset as i64,
								},
								ty: ptr_ty,
							}),
						},
						ty: ptr_ty,
					}
				}
			}
			tir::ExprKind::Store { target, value } => {
				let (ptr, offset, memory) =
					self.lower_place_address(func_ctx, target, sink);
				let lowered_value =
					self.lower_expression(func_ctx, value, sink);
				Expression {
					kind: ExprKind::PointerStore {
						pointer: Box::new(ptr),
						value: Box::new(lowered_value),
						offset,
						memory,
					},
					ty: ValueType::Unit,
				}
			}
			tir::ExprKind::Assign { left, right } => Expression {
				kind: self.lower_assignment(func_ctx, left, right, sink),
				ty: ValueType::Unit,
			},
			tir::ExprKind::CompoundAssign {
				target,
				rhs,
				method_id,
			} => self
				.lower_compound_assign(func_ctx, target, rhs, *method_id, sink),
			tir::ExprKind::GenericCompoundAssign {
				target,
				rhs,
				abstract_method_id,
				self_type,
			} => {
				let method_id = self.resolve_generic_compound_method(
					*abstract_method_id,
					*self_type,
				);
				self.lower_compound_assign(
					func_ctx, target, rhs, method_id, sink,
				)
			}
			tir::ExprKind::CompoundStore {
				target,
				rhs,
				method_id,
			} => self
				.lower_compound_store(func_ctx, target, rhs, *method_id, sink),
			tir::ExprKind::GenericCompoundStore {
				target,
				rhs,
				abstract_method_id,
				self_type,
			} => {
				let method_id = self.resolve_generic_compound_method(
					*abstract_method_id,
					*self_type,
				);
				self.lower_compound_store(
					func_ctx, target, rhs, method_id, sink,
				)
			}
		}
	}
}
