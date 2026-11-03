//! TIR → MIR lowering for the first executable checkpoint.
//!
//! This is deliberately not a view or a second IR: it takes the live
//! [`TypeContext`] the checker already built, reads the checked tables
//! directly, and constructs [`mir::MIR`]. Type normalization and aggregate
//! layout need `&mut TypeContext`, which is why the entry point is mutable.
//!
//! The current checkpoints cover exported functions, direct calls, locals,
//! blocks, returns, scalar operators, type aliases, and tuples and structs
//! (including generic and zero-sized fields). Aggregates keep their values in
//! declaration order while TIR supplies the byte offsets and size. Memory
//! types (arrays, slices, pointers) and function references are not lowered
//! yet. Every other checked form is reported as `UnsupportedExpression`;
//! nothing becomes `Noop` and no unsupported form disappears from the output.

use std::collections::{HashMap, HashSet, VecDeque};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::{Symbol, SymbolU32};

use super::body::{
	Body, ElementOrder, ExprIdx, ExprKind, PatternKind, ScopeIdx, ScopeKind,
};
use super::defs::{FieldIdx, FunctionIdx};
use super::layout::AggregateIdx;
use super::signatures::TypeContext;
use super::solver::{NormalizationDepth, RewriteFlags};
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::mir;
use crate::mir::layout::AggregateInterner;
use crate::vfs::FileId;

/// What one function's lowering keeps outside the shared [`Lowerer`].
struct FunctionState {
	file_id: FileId,
	/// The function's type environment; every body type is normalized there.
	env: TypeEnvIdx,
	function_id: mir::FunctionId,
	/// `body.locals()[i]` in the MIR local it was assigned.
	local_map: Vec<mir::LocalIndex>,
	/// MIR locals: the declared parameters first (including discard slots for
	/// unnamed ones), then every remaining source local.
	locals: Vec<mir::Local>,
	scopes: Vec<mir::BlockScope>,
	scope_map: HashMap<ScopeIdx, mir::ScopeIndex>,
}

struct Lowerer<'a, 'ast, 'ctx, 'dispatch> {
	context: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
	functions: Vec<mir::Function>,
	signatures: Vec<mir::FunctionSignature>,
	call_edges: Vec<(mir::FunctionId, mir::FunctionId)>,
	/// Backend identity, minted here. Never a source or Wasm index.
	ids: HashMap<FunctionIdx, mir::FunctionId>,
	/// TIR aggregate layouts already turned into MIR aggregates.
	aggregate_ids: HashMap<AggregateIdx, mir::AggregateIndex>,
	aggregates: AggregateInterner,
	pending: VecDeque<FunctionIdx>,
	next_id: u32,
}

/// The separate build entry point. `check` is untouched; this repeats its
/// setup and then lowers the same live context instead of dropping it.
pub(super) fn build(
	context: &mut TypeContext<'_, '_, '_>,
) -> Result<mir::MIR, ()> {
	Lowerer {
		context,
		functions: Vec::new(),
		signatures: Vec::new(),
		call_edges: Vec::new(),
		ids: HashMap::new(),
		aggregate_ids: HashMap::new(),
		aggregates: AggregateInterner::default(),
		pending: VecDeque::new(),
		next_id: 0,
	}
	.run()
}

impl<'a, 'ast, 'ctx, 'dispatch> Lowerer<'a, 'ast, 'ctx, 'dispatch> {
	fn run(mut self) -> Result<mir::MIR, ()> {
		let mut exports: Vec<(SymbolU32, super::signatures::ExportedItem)> =
			self.context
				.exports
				.iter()
				.map(|(&name, item)| (name, *item))
				.collect();
		// Deterministic export order, independent of hash iteration.
		exports.sort_by_key(|(name, _)| name.to_usize());

		let mut mir_exports = Vec::with_capacity(exports.len());
		for (name, item) in exports {
			match item {
				super::signatures::ExportedItem::Function(function) => {
					let id = self.enqueue(function);
					mir_exports.push(mir::ExportItem::Function { id, name });
				}
				super::signatures::ExportedItem::Global(_)
				| super::signatures::ExportedItem::Memory(_) => {
					let source = self
						.context
						.defs
						.exports
						.get(&name)
						.expect("every checked export has a source entry");
					self.unsupported(
						source.external_span.file_id,
						source.external_span.span,
						"exporting a global or a memory",
					)?;
				}
			}
		}

		while let Some(function) = self.pending.pop_front() {
			self.lower_function(function)?;
		}

		Ok(mir::MIR {
			functions: self.functions,
			inline_functions: HashSet::new(),
			signatures: self.signatures,
			globals: Vec::new(),
			exports: mir_exports,
			imports: Vec::new(),
			memories: Vec::new(),
			aggregates: self.aggregates.finish(),
			static_entries: Vec::new(),
			call_edges: self.call_edges,
			start_function: None,
		})
	}

	fn enqueue(&mut self, function: FunctionIdx) -> mir::FunctionId {
		if let Some(&id) = self.ids.get(&function) {
			return id;
		}
		let id = mir::FunctionId::new(self.next_id);
		self.next_id += 1;
		self.ids.insert(function, id);
		self.pending.push_back(function);
		id
	}

	fn lower_function(&mut self, function: FunctionIdx) -> Result<(), ()> {
		let id = self.ids[&function];
		let file_id =
			self.context.defs.functions[usize::from(function)].file_id;
		let (signature_index, param_types, result_type, env) =
			self.lower_signature(function)?;

		let Some(body) =
			self.context.function_bodies[usize::from(function)].take()
		else {
			self.unsupported(
				file_id,
				self.context.defs.functions[usize::from(function)].name.span,
				"a function without a body (imports are not lowered yet)",
			)?;
			unreachable!()
		};

		let lowered = self.lower_body(
			function,
			id,
			file_id,
			env,
			&body,
			&param_types,
			result_type,
		);
		// Put the checked body back: lowering borrows it, it does not consume it.
		self.context.function_bodies[usize::from(function)] = Some(body);
		let (scopes, locals, block) = lowered?;

		self.functions.push(mir::Function {
			id,
			signature_index,
			scopes,
			locals,
			block,
			static_data: Vec::new(),
		});
		Ok(())
	}

	fn lower_signature(
		&mut self,
		function: FunctionIdx,
	) -> Result<
		(
			mir::SignatureIndex,
			Vec<mir::ValueType>,
			mir::ValueType,
			TypeEnvIdx,
		),
		(),
	> {
		let (type_params, param_list, return_type) = {
			let signature = &self.context.functions[usize::from(function)];
			(
				signature.type_params,
				signature.param_types,
				signature.return_type,
			)
		};
		let file_id =
			self.context.defs.functions[usize::from(function)].file_id;
		let name_span =
			self.context.defs.functions[usize::from(function)].name.span;
		if !self.context.type_envs.param_names(type_params).is_empty() {
			self.unsupported(
				file_id,
				name_span,
				"generic functions (monomorphization is not implemented)",
			)?;
			unreachable!()
		}

		// Copy the list out so lowering a type may borrow the context mutably.
		let params: Vec<TypeIndex> =
			self.context.types.list(param_list).to_vec();
		let mut param_types = Vec::with_capacity(params.len());
		for ty in params {
			param_types.push(self.lower_type(
				ty,
				type_params,
				file_id,
				name_span,
			)?);
		}
		let result_type =
			self.lower_type(return_type, type_params, file_id, name_span)?;

		let mut items = param_types.clone();
		items.push(result_type);
		let index =
			self.intern_signature(items.into_boxed_slice(), param_types.len());
		Ok((index, param_types, result_type, type_params))
	}

	fn intern_signature(
		&mut self,
		items: Box<[mir::ValueType]>,
		params_count: usize,
	) -> mir::SignatureIndex {
		for (index, signature) in self.signatures.iter().enumerate() {
			if signature.params_count == params_count
				&& signature.items == items
			{
				return mir::SignatureIndex::new(index as u32);
			}
		}
		let index = mir::SignatureIndex::new(self.signatures.len() as u32);
		self.signatures.push(mir::FunctionSignature {
			items,
			params_count,
		});
		index
	}

	fn lower_body(
		&mut self,
		function: FunctionIdx,
		function_id: mir::FunctionId,
		file_id: FileId,
		env: TypeEnvIdx,
		body: &Body,
		param_types: &[mir::ValueType],
		result_type: mir::ValueType,
	) -> Result<(Vec<mir::BlockScope>, Vec<mir::Local>, mir::Expression), ()> {
		if body.params().len() != param_types.len() {
			self.unsupported(
				file_id,
				self.context.defs.functions[usize::from(function)].name.span,
				"a parameter list that does not match its checked signature",
			)?;
		}

		let mut state = FunctionState {
			file_id,
			env,
			function_id,
			local_map: vec![mir::LocalIndex::new(0); body.locals().len()],
			locals: Vec::new(),
			scopes: Vec::new(),
			scope_map: HashMap::new(),
		};

		// Parameters occupy the first `params_count` MIR locals, in order —
		// the contract `opt::builder` relies on. An unnamed parameter still
		// gets a discard local so the indices stay positional.
		for (position, binding) in body.params().iter().enumerate() {
			let index = mir::LocalIndex::new(state.locals.len() as u32);
			state.locals.push(mir::Local {
				ty: param_types[position],
				mutability: mir::Mutability::Immutable,
			});
			if let Some(local) = binding {
				state.local_map[usize::from(*local)] = index;
			}
		}
		// Every non-parameter local, in declaration order.
		for (tir_index, local) in body.locals().iter().enumerate() {
			if body
				.params()
				.iter()
				.flatten()
				.any(|&p| usize::from(p) == tir_index)
			{
				continue;
			}
			let ty =
				self.lower_type(local.ty, env, file_id, local.name.span)?;
			let index = mir::LocalIndex::new(state.locals.len() as u32);
			state.locals.push(mir::Local {
				ty,
				mutability: if local.mut_span.is_some() {
					mir::Mutability::Mutable
				} else {
					mir::Mutability::Immutable
				},
			});
			state.local_map[tir_index] = index;
		}

		let block = self.lower_expr(body, &mut state, body.root())?;
		if block.ty != result_type
			&& block.ty != mir::ValueType::Never
			&& block.ty != mir::ValueType::Unit
		{
			self.unsupported(
				file_id,
				body.span(body.root()),
				"a function body whose type differs from its declared result",
			)?;
		}

		Ok((state.scopes, state.locals, block))
	}

	fn lower_expr(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
	) -> Result<mir::Expression, ()> {
		let ty = self.lower_type(
			body.ty(expr),
			state.env,
			state.file_id,
			body.span(expr),
		)?;
		let kind = body.kind(expr);
		match kind {
			ExprKind::Int(bits) => {
				let kind = match ty {
					mir::ValueType::F32 => {
						mir::ExprKind::Float { value: bits as f64 }
					}
					mir::ValueType::F64 => {
						mir::ExprKind::Float { value: bits as f64 }
					}
					_ => mir::ExprKind::Int { value: bits as i64 },
				};
				Ok(mir::Expression { kind, ty })
			}
			ExprKind::Float(value) => Ok(mir::Expression {
				kind: mir::ExprKind::Float { value },
				ty,
			}),
			ExprKind::Local(local) => Ok(mir::Expression {
				kind: mir::ExprKind::LocalGet {
					local_index: state.local_map[usize::from(local)],
				},
				ty,
			}),
			ExprKind::PrimitiveUnary { op, operand } => {
				let operand = Box::new(self.lower_expr(body, state, operand)?);
				let kind = match op {
					UnaryOp::InvertSign => {
						mir::ExprKind::Neg { value: operand }
					}
					UnaryOp::Not => mir::ExprKind::Eqz { value: operand },
					UnaryOp::BitNot => mir::ExprKind::BitNot { value: operand },
				};
				Ok(mir::Expression { kind, ty })
			}
			ExprKind::PrimitiveBinary { op, lhs, rhs } => {
				let left = Box::new(self.lower_expr(body, state, lhs)?);
				let right = Box::new(self.lower_expr(body, state, rhs)?);
				let kind = match self.binary_kind(op, left, right) {
					Some(kind) => kind,
					None => {
						self.unsupported(
							state.file_id,
							body.span(expr),
							"an assignment operator in a value position",
						)?;
						unreachable!()
					}
				};
				Ok(mir::Expression { kind, ty })
			}
			ExprKind::Call {
				function,
				type_args,
				args,
			} => {
				if !type_args.is_empty() {
					self.unsupported(
						state.file_id,
						body.span(expr),
						"a call with type arguments",
					)?;
				}
				let callee_id = self.enqueue(function);
				let (callee_signature, callee_params, ..) =
					self.lower_signature(function)?;
				// A lone argument is its parameter's value, so it must not be
				// unpacked even when that value is itself a tuple.
				let arguments = if callee_params.len() == 1 {
					vec![self.lower_expr(body, state, args)?]
				} else {
					self.lower_arguments(body, state, args)?
				};
				self.call_edges.push((state.function_id, callee_id));
				Ok(mir::Expression {
					kind: mir::ExprKind::Call {
						callee: Box::new(mir::Expression {
							kind: mir::ExprKind::Function { id: callee_id },
							ty: mir::ValueType::Function {
								signature_index: callee_signature,
							},
						}),
						arguments: arguments.into_boxed_slice(),
					},
					ty,
				})
			}
			ExprKind::Tuple { elements, order } => {
				if ty == mir::ValueType::Unit {
					// `()` is the empty tuple; its only value is Unit.
					Ok(mir::Expression {
						kind: mir::ExprKind::Noop,
						ty,
					})
				} else {
					let values =
						self.lower_element_list(body, state, elements, order)?;
					self.build_aggregate(body, state, expr, values, ty)
				}
			}
			ExprKind::StructConstructor {
				struct_index: _,
				fields,
			} => {
				let values = self
					.lower_aggregate_elements(body, state, expr, fields, ty)?;
				self.build_aggregate(body, state, expr, values, ty)
			}
			ExprKind::FieldAccess { object, field } => {
				self.lower_field_access(body, state, expr, object, field, ty)
			}
			ExprKind::Block {
				scope,
				statements,
				result,
			} => {
				let scope_index = self.scope_for(body, state, scope, ty)?;
				let mut expressions = Vec::new();
				for statement in body.args(statements) {
					expressions.push(self.lower_expr(body, state, *statement)?);
				}
				if let Some(result) = result {
					expressions.push(self.lower_expr(body, state, result)?);
				}
				Ok(mir::Expression {
					kind: mir::ExprKind::Block {
						scope_index,
						expressions: expressions.into_boxed_slice(),
					},
					ty,
				})
			}
			ExprKind::LocalDeclaration { pattern, value } => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				match body.pattern(pattern) {
					PatternKind::Bind(local) => Ok(mir::Expression {
						kind: mir::ExprKind::LocalSet {
							local_index: state.local_map[usize::from(local)],
							value,
						},
						ty: mir::ValueType::Unit,
					}),
					PatternKind::Wildcard => Ok(mir::Expression {
						kind: mir::ExprKind::Drop { value },
						ty: mir::ValueType::Unit,
					}),
					_ => {
						self.unsupported(
							state.file_id,
							body.span(expr),
							"a destructuring local declaration",
						)?;
						unreachable!()
					}
				}
			}
			ExprKind::Assign { target, value } => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				match body.kind(target) {
					ExprKind::Local(local) => Ok(mir::Expression {
						kind: mir::ExprKind::LocalSet {
							local_index: state.local_map[usize::from(local)],
							value,
						},
						ty,
					}),
					ExprKind::FieldAccess { object, field }
						if matches!(body.kind(object), ExprKind::Local(_)) =>
					{
						let ExprKind::Local(local) = body.kind(object) else {
							unreachable!("guarded by the match above")
						};
						Ok(mir::Expression {
							kind: mir::ExprKind::AggregateSet {
								local_index: state.local_map
									[usize::from(local)],
								value_index: mir::FieldIndex::new(u32::from(
									field,
								)),
								value,
							},
							ty: mir::ValueType::Unit,
						})
					}
					_ => {
						self.unsupported(
							state.file_id,
							body.span(expr),
							"an assignment to a nested field",
						)?;
						unreachable!()
					}
				}
			}
			ExprKind::Drop { value } => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				Ok(mir::Expression {
					kind: mir::ExprKind::Drop { value },
					ty,
				})
			}
			ExprKind::Return { value } => {
				let value = match value {
					Some(value) => {
						Some(Box::new(self.lower_expr(body, state, value)?))
					}
					None => None,
				};
				Ok(mir::Expression {
					kind: mir::ExprKind::Return { value },
					ty,
				})
			}

			// Checked forms the first checkpoint does not lower yet. Listed
			// exhaustively so a new TIR variant forces a decision here.
			ExprKind::Error
			| ExprKind::Char(_)
			| ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. }
			| ExprKind::Const { .. }
			| ExprKind::AbstractConst { .. }
			| ExprKind::NextDiscriminant(_)
			| ExprKind::Global(_)
			| ExprKind::Function { .. }
			| ExprKind::AbstractCall { .. }
			| ExprKind::MethodCall { .. }
			| ExprKind::AbstractMethodCall { .. }
			| ExprKind::CallRef { .. }
			| ExprKind::Load(_)
			| ExprKind::AddressOf(_)
			| ExprKind::Match { .. }
			| ExprKind::IfElse { .. }
			| ExprKind::Loop { .. }
			| ExprKind::Break { .. }
			| ExprKind::Continue { .. }
			| ExprKind::Store { .. }
			| ExprKind::PrimitiveCompoundAssign { .. }
			| ExprKind::ConcreteCompoundAssign { .. }
			| ExprKind::AbstractCompoundAssign { .. }
			| ExprKind::PrimitiveCompoundStore { .. }
			| ExprKind::ConcreteCompoundStore { .. }
			| ExprKind::AbstractCompoundStore { .. } => {
				self.unsupported(
					state.file_id,
					body.span(expr),
					"this expression",
				)?;
				unreachable!()
			}
		}
	}

	/// Lower a call's argument value into one MIR argument per parameter, in
	/// parameter order. The TIR value is a tuple with its written-order
	/// permutation, or the single value of a one-parameter call.
	fn lower_arguments(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		args: ExprIdx,
	) -> Result<Vec<mir::Expression>, ()> {
		let ExprKind::Tuple { elements, order } = body.kind(args) else {
			return Ok(vec![self.lower_expr(body, state, args)?]);
		};
		self.lower_element_list(body, state, elements, order)
	}

	/// Lower an element list in written order, then put it in declaration
	/// order using its checked permutation. This covers calls, tuples, and
	/// struct constructors alike.
	fn lower_element_list(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		elements: super::body::ExprRange,
		order: ElementOrder,
	) -> Result<Vec<mir::Expression>, ()> {
		let written = body.args(elements);
		let mut lowered = Vec::with_capacity(written.len());
		for element in written {
			lowered.push(self.lower_expr(body, state, *element)?);
		}
		match order {
			ElementOrder::InOrder => Ok(lowered),
			ElementOrder::Permuted { .. } => {
				let mut slots: Vec<Option<mir::Expression>> =
					(0..lowered.len()).map(|_| None).collect();
				for (at, value) in lowered.into_iter().enumerate() {
					let declared = body.declared_index(order, at);
					slots[usize::from(declared)] = Some(value);
				}
				Ok(slots
					.into_iter()
					.map(|slot| {
						slot.expect(
							"a checked permutation names every element once",
						)
					})
					.collect())
			}
		}
	}

	/// A struct constructor's fields: the single field's own value, or the
	/// written argument list. A one-field struct must not unpack a tuple that
	/// is that field's value.
	fn lower_aggregate_elements(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		fields: ExprIdx,
		ty: mir::ValueType,
	) -> Result<Vec<mir::Expression>, ()> {
		let expected = self.aggregate_field_count(body, state, expr, ty)?;
		match expected {
			0 => Ok(Vec::new()),
			1 => Ok(vec![self.lower_expr(body, state, fields)?]),
			_ => self.lower_arguments(body, state, fields),
		}
	}

	fn aggregate_field_count(
		&mut self,
		body: &Body,
		state: &FunctionState,
		expr: ExprIdx,
		ty: mir::ValueType,
	) -> Result<usize, ()> {
		let mir::ValueType::Aggregate { aggregate_index } = ty else {
			self.unsupported(
				state.file_id,
				body.span(expr),
				"an aggregate whose type is not an aggregate",
			)?;
			unreachable!()
		};
		Ok(self.aggregates.get(aggregate_index).field_count())
	}

	/// Build an aggregate literal and check it has one value per declaration
	/// field, including zero-sized fields (whose value is `Unit`).
	fn build_aggregate(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		values: Vec<mir::Expression>,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		let expected = self.aggregate_field_count(body, state, expr, ty)?;
		if values.len() != expected {
			self.unsupported(
				state.file_id,
				body.span(expr),
				"an aggregate literal whose field count does not match its type",
			)?;
		}
		Ok(mir::Expression {
			kind: mir::ExprKind::Aggregate {
				values: values.into_boxed_slice(),
			},
			ty,
		})
	}

	/// `object.field`. `AggregateGet` addresses a local, so an object that is
	/// not already one is parked in a fresh temporary inside a small block,
	/// which keeps the object's evaluation exactly once.
	fn lower_field_access(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		object: ExprIdx,
		field: FieldIdx,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		let object_value = self.lower_expr(body, state, object)?;
		let field_index = mir::FieldIndex::new(u32::from(field));
		if let mir::ExprKind::LocalGet { local_index } = &object_value.kind {
			return Ok(mir::Expression {
				kind: mir::ExprKind::AggregateGet {
					local_index: *local_index,
					value_index: field_index,
				},
				ty,
			});
		}
		let temp = self.push_temp_local(state, object_value.ty);
		let scope = self.push_synthetic_scope(state, ty);
		Ok(mir::Expression {
			kind: mir::ExprKind::Block {
				scope_index: scope,
				expressions: Box::new([
					mir::Expression {
						kind: mir::ExprKind::LocalSet {
							local_index: temp,
							value: Box::new(object_value),
						},
						ty: mir::ValueType::Unit,
					},
					mir::Expression {
						kind: mir::ExprKind::AggregateGet {
							local_index: temp,
							value_index: field_index,
						},
						ty,
					},
				]),
			},
			ty,
		})
	}

	fn push_temp_local(
		&mut self,
		state: &mut FunctionState,
		ty: mir::ValueType,
	) -> mir::LocalIndex {
		let index = mir::LocalIndex::new(state.locals.len() as u32);
		state.locals.push(mir::Local {
			ty,
			mutability: mir::Mutability::Mutable,
		});
		index
	}

	/// A compiler-made scope, used only to sequence a temporary. No source
	/// `break` targets it, so `opt` builds it transparently.
	fn push_synthetic_scope(
		&mut self,
		state: &mut FunctionState,
		result: mir::ValueType,
	) -> mir::ScopeIndex {
		let index = mir::ScopeIndex::new(state.scopes.len() as u32);
		state.scopes.push(mir::BlockScope {
			kind: mir::BlockKind::Block,
			result,
		});
		index
	}

	fn scope_for(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		scope: ScopeIdx,
		result: mir::ValueType,
	) -> Result<mir::ScopeIndex, ()> {
		if let Some(&index) = state.scope_map.get(&scope) {
			return Ok(index);
		}
		let kind = match body.scope(scope).kind {
			ScopeKind::Block => mir::BlockKind::Block,
			ScopeKind::Loop => mir::BlockKind::Loop,
		};
		let index = mir::ScopeIndex::new(state.scopes.len() as u32);
		state.scopes.push(mir::BlockScope { kind, result });
		state.scope_map.insert(scope, index);
		Ok(index)
	}

	fn binary_kind(
		&self,
		op: BinaryOp,
		left: Box<mir::Expression>,
		right: Box<mir::Expression>,
	) -> Option<mir::ExprKind> {
		Some(match op {
			BinaryOp::Add => mir::ExprKind::Add { left, right },
			BinaryOp::Sub => mir::ExprKind::Sub { left, right },
			BinaryOp::Mul => mir::ExprKind::Mul { left, right },
			BinaryOp::Div => mir::ExprKind::Div { left, right },
			BinaryOp::Rem => mir::ExprKind::Rem { left, right },
			BinaryOp::Eq => mir::ExprKind::Eq { left, right },
			BinaryOp::NotEq => mir::ExprKind::NotEq { left, right },
			BinaryOp::Less => mir::ExprKind::Less { left, right },
			BinaryOp::LessEq => mir::ExprKind::LessEq { left, right },
			BinaryOp::Greater => mir::ExprKind::Greater { left, right },
			BinaryOp::GreaterEq => mir::ExprKind::GreaterEq { left, right },
			BinaryOp::And => mir::ExprKind::And { left, right },
			BinaryOp::Or => mir::ExprKind::Or { left, right },
			BinaryOp::BitAnd => mir::ExprKind::BitAnd { left, right },
			BinaryOp::BitOr => mir::ExprKind::BitOr { left, right },
			BinaryOp::BitXor => mir::ExprKind::BitXor { left, right },
			BinaryOp::LeftShift => mir::ExprKind::LeftShift { left, right },
			BinaryOp::RightShift => mir::ExprKind::RightShift { left, right },
			BinaryOp::Assign
			| BinaryOp::AddAssign
			| BinaryOp::SubAssign
			| BinaryOp::MulAssign
			| BinaryOp::DivAssign
			| BinaryOp::RemAssign
			| BinaryOp::BitAndAssign
			| BinaryOp::BitOrAssign
			| BinaryOp::BitXorAssign
			| BinaryOp::LeftShiftAssign
			| BinaryOp::RightShiftAssign => return None,
		})
	}

	/// The one type funnel: checked TIR type → MIR value type. Anything not
	/// fully concrete is a lowering error, never an accidental `Unit`.
	/// The one type funnel: checked TIR type → MIR value type.
	///
	/// Normalization runs through the live context first, so an alias, an
	/// associated-type projection the solver can resolve, or a constant in a
	/// type reaches MIR as its concrete type. Anything still not fully
	/// concrete is a lowering error with a source location, never an
	/// accidental `Unit`.
	fn lower_type(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		let ty = match self.context.normalize(
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		) {
			Ok(normalized) => normalized,
			Err(_) => {
				self.unsupported(
					file_id,
					span,
					"a type that does not normalize",
				)?;
				unreachable!()
			}
		};
		if ty == TypeIndex::UNIT {
			return Ok(mir::ValueType::Unit);
		}
		if ty == TypeIndex::NEVER {
			return Ok(mir::ValueType::Never);
		}
		let lowered = match *self.context.types.resolve(ty) {
			Type::U8 => mir::ValueType::U8,
			Type::I8 => mir::ValueType::I8,
			Type::U16 => mir::ValueType::U16,
			Type::I16 => mir::ValueType::I16,
			Type::U32 => mir::ValueType::U32,
			Type::I32 => mir::ValueType::I32,
			Type::U64 => mir::ValueType::U64,
			Type::I64 => mir::ValueType::I64,
			Type::F32 => mir::ValueType::F32,
			Type::F64 => mir::ValueType::F64,
			Type::Never => mir::ValueType::Never,
			Type::Enum { enum_index }
				if Some(enum_index) == self.context.defs.intrinsics.bool =>
			{
				mir::ValueType::Bool
			}
			Type::Enum { enum_index } => {
				let repr = self.context.enums[usize::from(enum_index)].repr;
				self.lower_type(repr, env, file_id, span)?
			}
			Type::Tuple { .. } | Type::Struct { .. } => {
				return self.lower_aggregate_type(ty, env, file_id, span);
			}
			Type::Pointer { .. } | Type::Array { .. } | Type::Slice { .. } => {
				self.unsupported(
					file_id,
					span,
					"a memory-backed type (the memory checkpoint)",
				)?;
				unreachable!()
			}
			Type::Funcref
			| Type::TypedFuncref { .. }
			| Type::Function { .. } => {
				self.unsupported(file_id, span, "a function reference type")?;
				unreachable!()
			}
			_ => {
				self.unsupported(
					file_id,
					span,
					"a type with no MIR representation",
				)?;
				unreachable!()
			}
		};
		Ok(lowered)
	}

	/// Lower a tuple or struct type to an aggregate, interning it once per
	/// TIR layout. TIR supplies the byte offsets and the aggregate's size and
	/// alignment; MIR keeps the declaration order.
	fn lower_aggregate_type(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		let aggregate = match self.context.aggregate_layout(env, ty) {
			Ok(Some(aggregate)) => aggregate,
			Ok(None) => {
				self.unsupported(
					file_id,
					span,
					"an aggregate without a layout",
				)?;
				unreachable!()
			}
			Err(_) => {
				self.unsupported(
					file_id,
					span,
					"an aggregate whose layout is not known",
				)?;
				unreachable!()
			}
		};
		if let Some(&index) = self.aggregate_ids.get(&aggregate) {
			return Ok(mir::ValueType::Aggregate {
				aggregate_index: index,
			});
		}

		let layout = self.context.aggregate(aggregate).clone();
		let field_types = self.aggregate_field_types(ty, env, file_id, span)?;
		if field_types.len() != layout.fields.len() {
			self.unsupported(
				file_id,
				span,
				"an aggregate whose fields do not match its layout",
			)?;
		}
		let mut fields = Vec::with_capacity(field_types.len());
		for field in field_types {
			fields.push(self.lower_type(field, env, file_id, span)?);
		}

		let index = {
			let size = layout.layout.size;
			let align = layout.layout.align;
			self.aggregates.intern(
				fields.into_boxed_slice(),
				layout.fields,
				mir::Layout { size, align },
			)
		};
		self.aggregate_ids.insert(aggregate, index);
		Ok(mir::ValueType::Aggregate {
			aggregate_index: index,
		})
	}

	/// A tuple's element types, or a struct's field types substituted with
	/// its type arguments, both in declaration order.
	fn aggregate_field_types(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<Vec<TypeIndex>, ()> {
		match *self.context.types.resolve(ty) {
			Type::Tuple { elements } => {
				Ok(self.context.types.list(elements).to_vec())
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let (signature_env, field_list) = {
					let signature =
						&self.context.structs[usize::from(struct_index)];
					(signature.type_params, signature.field_types)
				};
				let args: Box<[TypeIndex]> =
					self.context.types.list(type_args).into();
				let mut fields = Vec::with_capacity(field_list.len());
				for at in 0..field_list.len() {
					let field = self.context.types.list(field_list)[at];
					fields.push(self.context.types.substitute(
						field,
						Substitution {
							envs: &self.context.type_envs,
							env: signature_env,
							args: &args,
						},
					));
				}
				Ok(fields)
			}
			_ => {
				self.unsupported(
					file_id,
					span,
					"a non-aggregate type in aggregate position",
				)?;
				unreachable!()
			}
		}
	}

	fn unsupported(
		&mut self,
		file_id: FileId,
		span: TextSpan,
		what: &str,
	) -> Result<(), ()> {
		self.context.diagnostics.push(
			Diagnostic::bug()
				.with_code(DiagnosticCode::UnsupportedExpression.code())
				.with_message(format!("lowering {what} is not supported yet"))
				.with_label(Label::primary(file_id, span)),
		);
		Err(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Check, lower, encode, and instantiate `source`, returning the live
	/// store and instance for calling exports.
	fn instantiate(source: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir =
			crate::tir::build(&mut graph).expect("the checkpoint must lower");
		let module = crate::codegen::Builder::build(&mir, &graph.strings)
			.expect("lowered MIR must encode");
		let bytes = module.encode();
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, &bytes)
			.expect("lowered MIR must be valid Wasm");
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		(store, instance)
	}

	#[test]
	fn lowers_an_exported_scalar_add_to_runnable_mir() {
		let source = r#"
            func add(a: i32, b: i32) -> i32 { a + b }
            export { add as "add" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir =
			crate::tir::build(&mut graph).expect("a scalar add must lower");
		assert_eq!(mir.functions.len(), 1);
		assert_eq!(mir.signatures.len(), 1);
		assert_eq!(mir.exports.len(), 1);
		drop(graph);

		let (mut store, instance) = instantiate(source);
		let add = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "add")
			.expect("`add` must be exported");
		assert_eq!(add.call(&mut store, (5, 3)).unwrap(), 8);
	}

	#[test]
	fn lowers_direct_calls_and_a_local_initializer() {
		let source = r#"
            func double(x: i32) -> i32 { x * 2 }
            func plus_one(x: i32) -> i32 {
                local y: i32 = x + 1
                y
            }
            func main() -> i32 { plus_one(double(4)) }
            export { main as "main" }
        "#;
		let (mut store, instance) = instantiate(source);
		let main = instance
			.get_typed_func::<(), i32>(&mut store, "main")
			.expect("`main` must be exported");
		assert_eq!(main.call(&mut store, ()).unwrap(), 9);
	}

	#[test]
	fn normalizes_an_alias_through_the_live_context() {
		let source = r#"
            type Count = i32;
            func add(a: Count, b: Count) -> Count { a + b }
            export { add as "add" }
        "#;
		let (mut store, instance) = instantiate(source);
		let add = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "add")
			.expect("`add` must be exported");
		assert_eq!(add.call(&mut store, (20, 22)).unwrap(), 42);
	}

	#[test]
	fn reports_an_unsupported_form_instead_of_emitting_a_module() {
		let source = r#"
            func pick(x: i32) -> i32 {
                if x == x { 1 } else { 0 }
            }
            export { pick as "pick" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let diagnostics = match crate::tir::build(&mut graph) {
			Ok(_) => panic!("`if` has no lowering yet"),
			Err(diagnostics) => diagnostics,
		};
		assert!(
			diagnostics.iter().any(|d| {
				d.code.as_deref()
					== Some(DiagnosticCode::UnsupportedExpression.code())
			}),
			"expected an UnsupportedExpression diagnostic, got {diagnostics:#?}"
		);
	}

	#[test]
	fn reports_a_memory_type_as_unsupported() {
		let source = r#"
            memory heap: u32;
            func peek(p: heap::*i32) -> i32 { p.* }
            export { peek as "peek" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let diagnostics = match crate::tir::build(&mut graph) {
			Ok(_) => panic!("memory types have no lowering yet"),
			Err(diagnostics) => diagnostics,
		};
		assert!(
			diagnostics.iter().any(|d| {
				d.message.contains("memory checkpoint")
					&& d.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code())
			}),
			"expected the memory-checkpoint diagnostic, got {diagnostics:#?}"
		);
	}

	#[test]
	fn lowers_struct_construction_field_access_and_assignment() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func first(p: Point) -> i32 { p.x }
            func local_field() -> i32 {
                local mut p: Point = Point(10, 20)
                p.y = 5
                p.x + p.y
            }
            func call_field() -> i32 { Point(7, 9).x }
            func run() -> i32 {
                first(Point(3, 4)) + local_field() + call_field()
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 25);
	}

	#[test]
	fn lowers_nested_field_access() {
		let source = r#"
            struct Inner(a: i32, b: i32);
            struct Outer(inner: Inner, c: i32);
            func pick(o: Outer) -> i32 { o.inner.b }
            func run() -> i32 { pick(Outer(Inner(1, 2), 3)) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 2);
	}

	#[test]
	fn mixed_alignment_aggregate_keeps_declaration_value_order() {
		let source = r#"
            struct Mixed(a: u8, b: i64, c: u8);
            func take(m: Mixed) -> i64 { m.b + 1 }
            func run() -> i64 { take(Mixed(1, 1000000000000, 2)) }
            export { run as "run" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir =
			crate::tir::build(&mut graph).expect("the aggregate must lower");

		let aggregate = mir
			.aggregates
			.iter()
			.find(|aggregate| {
				aggregate.fields.iter().map(|f| f.ty).eq([
					mir::ValueType::U8,
					mir::ValueType::I64,
					mir::ValueType::U8,
				])
			})
			.expect("the struct's aggregate must be interned");
		let offsets: Vec<u32> =
			aggregate.fields.iter().map(|field| field.offset).collect();
		assert_eq!(offsets, vec![8, 0, 9], "TIR decides the byte offsets");

		let scalar_types: Vec<mir::ValueType> =
			aggregate.scalars.iter().map(|scalar| scalar.ty).collect();
		assert_eq!(
			scalar_types,
			vec![mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8],
			"scalar slots stay in declaration order"
		);
		drop(graph);

		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i64>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 1_000_000_000_001);
	}

	#[test]
	fn lowers_tuple_values_as_aggregates() {
		let source = r#"
            func identity(t: (i32, i32)) -> (i32, i32) { t }
            func run() -> (i32, i32) { identity((3, 4)) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), (i32, i32)>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), (3, 4));
	}

	#[test]
	fn instantiates_a_generic_struct_field_type() {
		let source = r#"
            struct Pair<T>(first: T, second: T);
            func sum(p: Pair<i32>) -> i32 { p.first + p.second }
            func run() -> i32 { sum(Pair({ first: 3, second: 4 })) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 7);
	}

	#[test]
	fn lowers_a_nested_generic_struct() {
		let source = r#"
            struct Wrapper<T>(value: T);
            struct Pair<T>(a: T, b: T);
            func pick(p: Pair<Wrapper<i32>>) -> i32 { p.b.value }
            func run() -> i32 { pick(Pair(Wrapper(1), Wrapper(2))) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 2);
	}

	#[test]
	fn assigns_a_whole_aggregate_local() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func run() -> i32 {
                local mut p: Point = Point(1, 2)
                p = Point(3, 4)
                p.x * 10 + p.y
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 34);
	}

	#[test]
	fn lowers_a_zero_field_struct() {
		let source = r#"
            struct Marker();
            func make() -> Marker { Marker() }
            func run() -> i32 {
                local m: Marker = make()
                _ = m
                5
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 5);
	}

	#[test]
	fn drops_a_multi_scalar_aggregate_value() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func run() -> i32 {
                _ = Point(1, 2)
                5
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 5);
	}

	#[test]
	fn zero_sized_field_still_has_a_value_and_no_slot() {
		let source = r#"
            struct HasUnit(a: u8, u: (), b: u8);
            func last(w: HasUnit) -> u8 { w.b }
            func run() -> u8 { last(HasUnit(3, (), 4)) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, ()).unwrap(), 4);
	}
}
