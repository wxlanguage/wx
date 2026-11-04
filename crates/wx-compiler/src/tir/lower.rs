//! TIR → MIR lowering for the first executable checkpoint.
//!
//! This is deliberately not a view or a second IR: it takes the live
//! [`TypeContext`] the checker already built, reads the checked tables
//! directly, and constructs [`mir::MIR`]. Type normalization and aggregate
//! layout need `&mut TypeContext`, which is why the entry point is mutable.
//!
//! The current checkpoints cover exported functions, direct calls, method
//! calls, locals, blocks, returns, scalar operators (including
//! short-circuiting `&&`/`||`) and intrinsics, loops, breaks and continues
//! (including labelled blocks and loops), `if`/`else`, `match` (including
//! destructuring, `|` alternatives and char patterns), destructuring `local`
//! declarations, primitive and concrete compound assignments, concrete
//! constants (`True`/`False`, enum variants and free `const` items), `Char`
//! literals, type aliases, and tuples and structs (including generic and
//! zero-sized fields).
//! Aggregates keep their values in declaration order while TIR supplies the
//! byte offsets and size. A constant pattern compares an aggregate through
//! the concrete `PartialEq::eq` impl its checked `Eq` bound selects, so a
//! type's own equality is honoured. Memory types (arrays, slices, pointers),
//! abstract dispatch (`AbstractCall`/`AbstractMethodCall`), function
//! references, and float equality tests (floats have no total equality) are
//! not lowered yet. Every other checked form is reported as
//! `UnsupportedExpression`; no unsupported form becomes `Noop` and no
//! unsupported form disappears from the output.

use std::collections::{HashMap, HashSet, VecDeque};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::{Symbol, SymbolU32};

use super::body::{
	Body, ElementOrder, ExprIdx, ExprKind, FunctionImplementation, ScopeIdx,
	ScopeKind,
};
use super::defs::{FieldIdx, FunctionIdx};
use super::signatures::TypeContext;
use super::solver::{NormalizationDepth, RewriteFlags};
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex, TypeList};
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::{DiagnosticCode, TextSpan};
use crate::mir;
use crate::mir::layout::AggregateTable;
use crate::vfs::FileId;

mod constants;
mod intrinsics;
mod patterns;

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

/// Source field selections are lowering metadata, never MIR type structure.
/// Keep them once per normalized concrete type for constant-time projection.
struct AggregateLowering {
	ty: mir::ValueType,
	fields: Box<[mir::ScalarRange]>,
}

struct Lowerer<'a, 'ast, 'ctx, 'dispatch> {
	context: &'a mut TypeContext<'ast, 'ctx, 'dispatch>,
	functions: Vec<mir::Function>,
	signatures: Vec<mir::FunctionSignature>,
	call_edges: Vec<(mir::FunctionId, mir::FunctionId)>,
	/// Backend identity, minted here. Never a source or Wasm index.
	ids: HashMap<FunctionIdx, mir::FunctionId>,
	/// Concrete source types already translated into flat representations.
	aggregate_types: HashMap<TypeIndex, AggregateLowering>,
	aggregates: AggregateTable,
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
		aggregate_types: HashMap::new(),
		aggregates: AggregateTable::default(),
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
		let name_span =
			self.context.defs.functions[usize::from(function)].name.span;
		match &self.context.function_implementations[usize::from(function)] {
			FunctionImplementation::Defined(_) => {}
			FunctionImplementation::Intrinsic(_) => {
				self.unsupported(
					file_id,
					name_span,
					"exporting an intrinsic function (requires a wrapper)",
				)?;
			}
			FunctionImplementation::Imported(import) => {
				let name = self.context.defs.imports[usize::from(*import)]
					.external_name
					.inner;
				let name = self.context.strings.resolve(name).unwrap();
				self.unsupported(
					file_id,
					name_span,
					&format!("an imported function from `{name}`"),
				)?;
			}
			FunctionImplementation::Declaration => {
				let provided = matches!(
					self.context
						.ast_node(super::defs::DefId::Function(function)),
					super::defs::AstNodeRef::Function {
						item: crate::ast::Item::CrateFunction { .. },
						..
					}
				);
				self.unsupported(
					file_id,
					name_span,
					if provided {
						"an unfulfilled package function parameter"
					} else {
						"a function declaration without an implementation"
					},
				)?;
			}
		}
		let (signature_index, param_types, result_type, env) =
			self.lower_signature(function)?;

		let implementation = std::mem::replace(
			&mut self.context.function_implementations[usize::from(function)],
			FunctionImplementation::Declaration,
		);
		let lowered = self.lower_body(
			function,
			id,
			file_id,
			env,
			implementation
				.body()
				.expect("only a defined function enters body lowering"),
			&param_types,
			result_type,
		);
		// Put the checked body back: lowering borrows it, it does not consume it.
		self.context.function_implementations[usize::from(function)] =
			implementation;
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
				if ty == mir::ValueType::Never {
					// The operand diverges, so the operator never runs. Do
					// not make a `Never`-typed instruction out of it; the
					// operand's own expression already carries the
					// divergence and the effects that preceded it.
					debug_assert_eq!(body.ty(operand), TypeIndex::NEVER);
					let operand = self.lower_expr(body, state, operand)?;
					debug_assert_eq!(operand.ty, mir::ValueType::Never);
					return Ok(operand);
				}
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
				if matches!(op, BinaryOp::And | BinaryOp::Or) {
					return self.lower_short_circuit(body, state, op, lhs, rhs);
				}
				if ty == mir::ValueType::Never {
					// A `Never` result means both operands diverge, so the
					// operator is never applied and the right operand is
					// never evaluated.
					debug_assert_eq!(body.ty(rhs), TypeIndex::NEVER);
					let left = self.lower_expr(body, state, lhs)?;
					debug_assert_eq!(left.ty, mir::ValueType::Never);
					return Ok(left);
				}
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
				if let FunctionImplementation::Intrinsic(intrinsic) =
					self.context.function_implementations[usize::from(function)]
				{
					return self.lower_intrinsic(
						body, state, expr, intrinsic, args, ty,
					);
				}
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
				let mut prefix = Vec::new();
				let arguments = if callee_params.len() == 1 {
					vec![self.lower_expr(body, state, args)?]
				} else {
					self.lower_arguments(body, state, args, &mut prefix)?
				};
				let call = self.build_call(
					state,
					callee_id,
					callee_signature,
					arguments,
					ty,
				);
				Ok(self.sequence(state, prefix, call))
			}
			ExprKind::MethodCall {
				function,
				type_args,
				receiver,
				args,
			} => {
				if !type_args.is_empty() {
					self.unsupported(
						state.file_id,
						body.span(expr),
						"a method call with type arguments",
					)?;
				}
				let callee_id = self.enqueue(function);
				// The receiver is the first parameter and runs before the
				// remaining arguments.
				let receiver = self.lower_expr(body, state, receiver)?;
				let (callee_signature, callee_params, ..) =
					self.lower_signature(function)?;
				let mut prefix = Vec::new();
				let arguments = if callee_params.len() == 2 {
					// A lone remaining parameter is its value, not a tuple of
					// one.
					vec![self.lower_expr(body, state, args)?]
				} else {
					self.lower_arguments(body, state, args, &mut prefix)?
				};
				// Reordering or spilling the remaining arguments puts them in
				// `prefix`, which runs before the call's own arguments. Carry
				// the receiver through a temporary so it still runs first.
				let receiver = if prefix.is_empty() {
					receiver
				} else {
					let ty = receiver.ty;
					let local_index = self.push_temp_local(state, ty);
					prefix.insert(
						0,
						mir::Expression {
							kind: mir::ExprKind::LocalSet {
								local_index,
								value: Box::new(receiver),
							},
							ty: mir::ValueType::Unit,
						},
					);
					mir::Expression {
						kind: mir::ExprKind::LocalGet { local_index },
						ty,
					}
				};
				let mut call_arguments =
					Vec::with_capacity(arguments.len() + 1);
				call_arguments.push(receiver);
				call_arguments.extend(arguments);
				let call = self.build_call(
					state,
					callee_id,
					callee_signature,
					call_arguments,
					ty,
				);
				Ok(self.sequence(state, prefix, call))
			}
			ExprKind::Tuple { elements, order } => {
				if ty == mir::ValueType::Unit {
					// `()` is the empty tuple; its only value is Unit.
					Ok(mir::Expression {
						kind: mir::ExprKind::Noop,
						ty,
					})
				} else {
					let mut prefix = Vec::new();
					let values = self.lower_element_list(
						body,
						state,
						elements,
						order,
						&mut prefix,
					)?;
					let value =
						self.build_aggregate(body, state, expr, values, ty)?;
					Ok(self.sequence(state, prefix, value))
				}
			}
			ExprKind::StructConstructor {
				struct_index: _,
				fields,
			} => {
				let mut prefix = Vec::new();
				let values = self.lower_aggregate_elements(
					body,
					state,
					expr,
					fields,
					&mut prefix,
				)?;
				let value =
					self.build_aggregate(body, state, expr, values, ty)?;
				Ok(self.sequence(state, prefix, value))
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
			ExprKind::Loop { scope, statements } => {
				// A loop shares its scope with its body: `break` and
				// `continue` name it, so the body block is what `opt` builds
				// as the loop. Register the scope before its statements so
				// jumps inside already see it.
				let scope_index = self.scope_for(body, state, scope, ty)?;
				let mut expressions = Vec::new();
				for statement in body.args(statements) {
					expressions.push(self.lower_expr(body, state, *statement)?);
				}
				// A body runs repeatedly and yields nothing; only a `break`
				// leaves the loop with a value.
				let block = mir::Expression {
					kind: mir::ExprKind::Block {
						scope_index,
						expressions: expressions.into_boxed_slice(),
					},
					ty: mir::ValueType::Unit,
				};
				Ok(mir::Expression {
					kind: mir::ExprKind::Loop {
						scope_index,
						block: Box::new(block),
					},
					ty,
				})
			}
			ExprKind::Break { scope, value } => {
				let scope_index = self.jump_scope(body, state, scope)?;
				let value = match value {
					Some(value) => {
						Some(Box::new(self.lower_expr(body, state, value)?))
					}
					None => None,
				};
				Ok(mir::Expression {
					kind: mir::ExprKind::Break { scope_index, value },
					ty,
				})
			}
			ExprKind::Continue { scope } => {
				let scope_index = self.jump_scope(body, state, scope)?;
				Ok(mir::Expression {
					kind: mir::ExprKind::Continue { scope_index },
					ty,
				})
			}
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let condition =
					Box::new(self.lower_expr(body, state, condition)?);
				let then_block =
					Box::new(self.lower_branch(body, state, then_block)?);
				let else_block = match else_block {
					Some(else_block) => Some(Box::new(
						self.lower_branch(body, state, else_block)?,
					)),
					None => None,
				};
				Ok(mir::Expression {
					kind: mir::ExprKind::IfElse {
						condition,
						then_block,
						else_block,
					},
					ty,
				})
			}
			ExprKind::Char(value) => {
				let codepoint = i64::from(u32::from(value));
				match ty {
					// The `Char` struct itself: one `u32` codepoint.
					mir::ValueType::Aggregate { aggregate_index } => {
						debug_assert_eq!(
							self.aggregates
								.get(aggregate_index)
								.scalars
								.as_ref(),
							[mir::ValueType::U32],
							"`Char` is one `u32` codepoint"
						);
						Ok(mir::Expression {
							kind: mir::ExprKind::Aggregate {
								values: Box::new([mir::Expression {
									kind: mir::ExprKind::Int {
										value: codepoint,
									},
									ty: mir::ValueType::U32,
								}]),
							},
							ty,
						})
					}
					// `coerce_char` turns a character literal into that
					// integer's value when its context is an integer type.
					_ => {
						debug_assert!(
							matches!(
								ty,
								mir::ValueType::I8
									| mir::ValueType::U8 | mir::ValueType::I16
									| mir::ValueType::U16 | mir::ValueType::I32
									| mir::ValueType::U32 | mir::ValueType::I64
									| mir::ValueType::U64
							),
							"a character literal's non-`Char` type is an integer"
						);
						Ok(mir::Expression {
							kind: mir::ExprKind::Int { value: codepoint },
							ty,
						})
					}
				}
			}
			ExprKind::Match { scrutinee, arms } => {
				self.lower_match(body, state, scrutinee, arms, ty)
			}
			ExprKind::Const {
				constant,
				type_args,
			} => self.lower_constant(body, state, expr, constant, type_args, ty),
			ExprKind::LocalDeclaration { pattern, value } => {
				self.lower_local_declaration(body, state, value, pattern, ty)
			}
			ExprKind::Assign { target, value } => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				self.write_target(body, state, target, value)
			}
			ExprKind::PrimitiveCompoundAssign { op, target, value } => self
				.lower_primitive_compound_assign(
					body,
					state,
					target,
					value,
					op,
					body.span(expr),
				),
			ExprKind::ConcreteCompoundAssign {
				method,
				type_args,
				target,
				value,
			} => self.lower_concrete_compound_assign(
				body,
				state,
				target,
				value,
				method,
				type_args,
				body.span(expr),
			),
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
			| ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. }
			| ExprKind::AbstractConst { .. }
			| ExprKind::NextDiscriminant(_)
			| ExprKind::Global(_)
			| ExprKind::Function { .. }
			| ExprKind::AbstractCall { .. }
			| ExprKind::AbstractMethodCall { .. }
			| ExprKind::CallRef { .. }
			| ExprKind::Load(_)
			| ExprKind::AddressOf(_)
			| ExprKind::Store { .. }
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

	/// The MIR node for a direct call to `callee_id`, recording the edge.
	/// `arguments` are already lowered in evaluation order and the callee's
	/// signature is already interned.
	fn build_call(
		&mut self,
		state: &mut FunctionState,
		callee_id: mir::FunctionId,
		signature_index: mir::SignatureIndex,
		arguments: Vec<mir::Expression>,
		ty: mir::ValueType,
	) -> mir::Expression {
		self.call_edges.push((state.function_id, callee_id));
		mir::Expression {
			kind: mir::ExprKind::Call {
				callee: Box::new(mir::Expression {
					kind: mir::ExprKind::Function { id: callee_id },
					ty: mir::ValueType::Function { signature_index },
				}),
				arguments: arguments.into_boxed_slice(),
			},
			ty,
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
		prefix: &mut Vec<mir::Expression>,
	) -> Result<Vec<mir::Expression>, ()> {
		let ExprKind::Tuple { elements, order } = body.kind(args) else {
			let value = self.lower_expr(body, state, args)?;
			let source_ty = self.normalize_type(body.ty(args), state.env, state.file_id, body.span(args))?;
			if !matches!(self.context.types.resolve(source_ty), Type::Tuple { .. }) {
				return Ok(vec![value]);
			}
			// A computed argument tuple is evaluated once. Its source fields
			// may each be a subpack or Unit, not necessarily a single slot.
			let local_index = self.push_temp_local(state, value.ty);
			prefix.push(mir::Expression { kind: mir::ExprKind::LocalSet { local_index, value: Box::new(value) }, ty: mir::ValueType::Unit });
			let field_types = self.aggregate_field_types(source_ty, state.env, state.file_id, body.span(args))?;
			let mut result = Vec::with_capacity(field_types.len());
			for (at, field_ty) in field_types.into_iter().enumerate() {
				let ty = self.lower_type(field_ty, state.env, state.file_id, body.span(args))?;
				let range = self.field_range(source_ty, state, FieldIdx::new(at as u32), body.span(args))?;
				result.push(mir::Expression { kind: mir::ExprKind::AggregateGet { local_index, range }, ty });
			}
			return Ok(result);
		};
		self.lower_element_list(body, state, elements, order, prefix)
	}

	/// Lower an element list in written order, then put it in declaration
	/// order using its checked permutation. For a permutation, append local
	/// initializers to `prefix` in written order and return local reads in
	/// declaration order. The caller must sequence `prefix` before using them.
	/// This covers calls, tuples, and struct constructors alike.
	fn lower_element_list(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		elements: super::body::ExprRange,
		order: ElementOrder,
		prefix: &mut Vec<mir::Expression>,
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
					let ty = value.ty;
					let local_index = self.push_temp_local(state, ty);
					prefix.push(mir::Expression {
						kind: mir::ExprKind::LocalSet {
							local_index,
							value: Box::new(value),
						},
						ty: mir::ValueType::Unit,
					});
					slots[usize::from(declared)] = Some(mir::Expression {
						kind: mir::ExprKind::LocalGet { local_index },
						ty,
					});
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
		prefix: &mut Vec<mir::Expression>,
	) -> Result<Vec<mir::Expression>, ()> {
		let expected = self.aggregate_field_types(body.ty(expr), state.env, state.file_id, body.span(expr))?.len();
		match expected {
			0 => Ok(Vec::new()),
			1 => Ok(vec![self.lower_expr(body, state, fields)?]),
			_ => self.lower_arguments(body, state, fields, prefix),
		}
	}

	/// Evaluate source field values once, then assemble only scalar slots.
	/// Source nesting and zero-sized fields do not survive into the pack.
	fn build_aggregate(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		values: Vec<mir::Expression>,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		let expected = self.aggregate_field_types(body.ty(expr), state.env, state.file_id, body.span(expr))?.len();
		if values.len() != expected {
			self.unsupported(
				state.file_id,
				body.span(expr),
				"an aggregate literal whose field count does not match its type",
			)?;
		}
		let mut prefix = Vec::with_capacity(values.len());
		let mut slots = Vec::with_capacity(self.slot_count(ty));
		for value in values {
			if value.ty == mir::ValueType::Never {
				return Ok(self.sequence(state, prefix, value));
			}
			if value.ty == mir::ValueType::Unit {
				prefix.push(mir::Expression { kind: mir::ExprKind::Drop { value: Box::new(value) }, ty: mir::ValueType::Unit });
				continue;
			}
			let value_ty = value.ty;
			let local_index = self.push_temp_local(state, value_ty);
			prefix.push(mir::Expression { kind: mir::ExprKind::LocalSet { local_index, value: Box::new(value) }, ty: mir::ValueType::Unit });
			match value_ty {
				mir::ValueType::Aggregate { aggregate_index } => {
					for (at, &ty) in self.aggregates.get(aggregate_index).scalars.iter().enumerate() {
						slots.push(mir::Expression { kind: mir::ExprKind::AggregateGet { local_index, range: mir::ScalarRange::new(at as u32, 1) }, ty });
					}
				}
				_ => slots.push(mir::Expression { kind: mir::ExprKind::LocalGet { local_index }, ty: value_ty }),
			}
		}
		let value = if ty == mir::ValueType::Unit {
			assert!(slots.is_empty());
			mir::Expression { kind: mir::ExprKind::Noop, ty }
		} else { mir::Expression {
			kind: mir::ExprKind::Aggregate {
				values: slots.into_boxed_slice(),
			},
			ty,
		} };
		Ok(self.sequence(state, prefix, value))
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
		// A chain rooted in a local needs just one absolute slot selection,
		// rather than a temporary subpack for every source field on the path.
		let mut root = object;
		while let ExprKind::FieldAccess { object, .. } = body.kind(root) {
			root = object;
		}
		if matches!(body.kind(root), ExprKind::Local(_)) {
			let (local_index, range) = self.local_projection(body, state, expr)?;
			return Ok(mir::Expression { kind: mir::ExprKind::AggregateGet { local_index, range }, ty });
		}
		let object_value = self.lower_expr(body, state, object)?;
		let range = self.field_range(body.ty(object), state, field, body.span(expr))?;
		if let mir::ExprKind::LocalGet { local_index } = &object_value.kind {
			return Ok(mir::Expression {
				kind: mir::ExprKind::AggregateGet {
					local_index: *local_index,
					range,
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
							range,
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

	/// Translate one source declaration field into slots. This map is local
	/// to lowering; the owned MIR contains neither field IDs nor field types.
	fn field_range(
		&mut self,
		ty: TypeIndex,
		state: &FunctionState,
		field: FieldIdx,
		span: TextSpan,
	) -> Result<mir::ScalarRange, ()> {
		let ty = self.normalize_type(ty, state.env, state.file_id, span)?;
		self.lower_type(ty, state.env, state.file_id, span)?;
		Ok(self.aggregate_types[&ty].fields[usize::from(field)])
	}

	/// A local field path has no address computation or runtime receiver.
	/// Compose its slot ranges without loading/reconstructing subaggregates.
	fn local_projection(
		&mut self,
		body: &Body,
		state: &FunctionState,
		target: ExprIdx,
	) -> Result<(mir::LocalIndex, mir::ScalarRange), ()> {
		match body.kind(target) {
			ExprKind::Local(local) => {
				let index = state.local_map[usize::from(local)];
				let len = self.slot_count(state.locals[usize::from(index)].ty);
				Ok((index, mir::ScalarRange::new(0, len as u32)))
			}
			ExprKind::FieldAccess { object, field } => {
				let (local, parent) = self.local_projection(body, state, object)?;
				let child = self.field_range(body.ty(object), state, field, body.span(target))?;
				assert!(child.indices().end <= parent.len as usize);
				Ok((local, mir::ScalarRange::new(u32::from(parent.start) + u32::from(child.start), child.len)))
			}
			_ => {
				self.unsupported(state.file_id, body.span(target), "a non-local assignment target")?;
				unreachable!()
			}
		}
	}

	/// Read an assignment target's current value. `target` is a local or a
	/// field path rooted in one; `local_projection` validates that and
	/// flattens the path to a slot range.
	fn read_target(
		&mut self,
		body: &Body,
		state: &FunctionState,
		target: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::Expression, ()> {
		let (local_index, range) =
			self.local_projection(body, state, target)?;
		let kind = if matches!(body.kind(target), ExprKind::Local(_)) {
			mir::ExprKind::LocalGet { local_index }
		} else {
			mir::ExprKind::AggregateGet { local_index, range }
		};
		Ok(mir::Expression { kind, ty })
	}

	/// Store `value`, already evaluated, into an assignment target. The
	/// target is a local or a flat field range rooted in one.
	fn write_target(
		&mut self,
		body: &Body,
		state: &FunctionState,
		target: ExprIdx,
		value: Box<mir::Expression>,
	) -> Result<mir::Expression, ()> {
		let (local_index, range) =
			self.local_projection(body, state, target)?;
		let kind = if matches!(body.kind(target), ExprKind::Local(_)) {
			mir::ExprKind::LocalSet { local_index, value }
		} else {
			mir::ExprKind::AggregateSet {
				local_index,
				range,
				value,
			}
		};
		Ok(mir::Expression {
			kind,
			ty: mir::ValueType::Unit,
		})
	}

	/// `target op= value` on a primitive scalar. The operand runs first, as
	/// in `target = target op value`; it is then read back from a temporary
	/// so the target is read only after that evaluation, the operator runs,
	/// and the result is stored.
	fn lower_primitive_compound_assign(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		target: ExprIdx,
		value: ExprIdx,
		op: BinaryOp,
		span: TextSpan,
	) -> Result<mir::Expression, ()> {
		let target_ty = self.lower_type(
			body.ty(target),
			state.env,
			state.file_id,
			body.span(target),
		)?;
		let value = self.lower_expr(body, state, value)?;
		if value.ty == mir::ValueType::Never {
			return Ok(value);
		}
		let value_ty = value.ty;
		let value_local = self.push_temp_local(state, value_ty);
		let prefix = vec![mir::Expression {
			kind: mir::ExprKind::LocalSet {
				local_index: value_local,
				value: Box::new(value),
			},
			ty: mir::ValueType::Unit,
		}];
		let read = self.read_target(body, state, target, target_ty)?;
		let operand = mir::Expression {
			kind: mir::ExprKind::LocalGet {
				local_index: value_local,
			},
			ty: value_ty,
		};
		let Some(kind) =
			self.binary_kind(op, Box::new(read), Box::new(operand))
		else {
			self.unsupported(
				state.file_id,
				span,
				"a compound assignment operator in a value position",
			)?;
			unreachable!()
		};
		let result = mir::Expression {
			kind,
			ty: target_ty,
		};
		let store = self.write_target(body, state, target, Box::new(result))?;
		Ok(self.sequence(state, prefix, store))
	}

	/// `target op= value` through a concrete impl's method. The operand runs
	/// first and is read back from a temporary; then the target is read as
	/// the receiver, the method runs, and its result is stored.
	fn lower_concrete_compound_assign(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		target: ExprIdx,
		value: ExprIdx,
		method: FunctionIdx,
		type_args: TypeList,
		span: TextSpan,
	) -> Result<mir::Expression, ()> {
		if !type_args.is_empty() {
			self.unsupported(
				state.file_id,
				span,
				"a compound assignment with type arguments",
			)?;
		}
		let target_ty = self.lower_type(
			body.ty(target),
			state.env,
			state.file_id,
			body.span(target),
		)?;
		let value = self.lower_expr(body, state, value)?;
		if value.ty == mir::ValueType::Never {
			return Ok(value);
		}
		let value_ty = value.ty;
		let value_local = self.push_temp_local(state, value_ty);
		let prefix = vec![mir::Expression {
			kind: mir::ExprKind::LocalSet {
				local_index: value_local,
				value: Box::new(value),
			},
			ty: mir::ValueType::Unit,
		}];
		let read = self.read_target(body, state, target, target_ty)?;
		let operand = mir::Expression {
			kind: mir::ExprKind::LocalGet {
				local_index: value_local,
			},
			ty: value_ty,
		};
		let callee_id = self.enqueue(method);
		let (callee_signature, callee_params, ..) =
			self.lower_signature(method)?;
		if callee_params.len() != 2 {
			self.unsupported(
				state.file_id,
				span,
				"a compound assignment method that is not a binary operator",
			)?;
			unreachable!()
		}
		let call = self.build_call(
			state,
			callee_id,
			callee_signature,
			vec![read, operand],
			target_ty,
		);
		let store = self.write_target(body, state, target, Box::new(call))?;
		Ok(self.sequence(state, prefix, store))
	}

	fn slot_count(&self, ty: mir::ValueType) -> usize {
		match ty {
			mir::ValueType::Unit => 0,
			mir::ValueType::Never => panic!("divergence is not an empty value"),
			mir::ValueType::Aggregate { aggregate_index } => self.aggregates.get(aggregate_index).scalars.len(),
			_ => 1,
		}
	}

	/// Run all setup expressions before producing `value`. In particular,
	/// spills must execute even when the final value owns no Wasm slots.
	fn sequence(
		&mut self,
		state: &mut FunctionState,
		mut prefix: Vec<mir::Expression>,
		value: mir::Expression,
	) -> mir::Expression {
		if prefix.is_empty() {
			return value;
		}
		let ty = value.ty;
		let scope_index = self.push_synthetic_scope(state, ty);
		prefix.push(value);
		mir::Expression {
			kind: mir::ExprKind::Block {
				scope_index,
				expressions: prefix.into_boxed_slice(),
			},
			ty,
		}
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

	/// An `if`'s branch. A source branch is a block, but `else if` puts an
	/// `if` where the else branch goes; MIR requires every branch to be a
	/// `Block`, so a non-block branch gets a transparent wrapper.
	fn lower_branch(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		branch: ExprIdx,
	) -> Result<mir::Expression, ()> {
		let value = self.lower_expr(body, state, branch)?;
		Ok(self.block_for_branch(state, value))
	}

	/// A branch value as the `Block` MIR requires. A source block already is
	/// one; a value synthesized by lowering (an `else if`'s nested `if`, or
	/// a short-circuit's constant) is wrapped in a block with its own
	/// synthetic scope, which has no source label and is transparent to
	/// `opt`.
	fn block_for_branch(
		&mut self,
		state: &mut FunctionState,
		value: mir::Expression,
	) -> mir::Expression {
		if matches!(value.kind, mir::ExprKind::Block { .. }) {
			return value;
		}
		let ty = value.ty;
		let scope_index = self.push_synthetic_scope(state, ty);
		mir::Expression {
			kind: mir::ExprKind::Block {
				scope_index,
				expressions: Box::new([value]),
			},
			ty,
		}
	}

	/// `&&` and `||` branch on the left operand, so the right one runs only
	/// when it decides the result. MIR's `And`/`Or` are bitwise on both
	/// operands, so the low-level form is an `IfElse`:
	/// `a && b` is `if a { b } else { false }`, and `a || b` is
	/// `if a { true } else { b }`. The left operand is evaluated exactly
	/// once, before either branch.
	fn lower_short_circuit(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		op: BinaryOp,
		lhs: ExprIdx,
		rhs: ExprIdx,
	) -> Result<mir::Expression, ()> {
		// A diverging operand is `!`, which fits the `Bool` expectation, so
		// it never produces a value for the branch.
		debug_assert!(matches!(
			body.ty(lhs),
			TypeIndex::BOOL | TypeIndex::NEVER
		));
		let condition = Box::new(self.lower_expr(body, state, lhs)?);
		let right = self.lower_expr(body, state, rhs)?;
		let literal = |value| mir::Expression::boolean(value);
		let (then_value, else_value) = match op {
			BinaryOp::And => (right, literal(false)),
			BinaryOp::Or => (literal(true), right),
			_ => unreachable!("only logical operators short-circuit"),
		};
		let then_block = Box::new(self.block_for_branch(state, then_value));
		let else_block = Box::new(self.block_for_branch(state, else_value));
		Ok(mir::Expression {
			kind: mir::ExprKind::IfElse {
				condition,
				then_block,
				else_block: Some(else_block),
			},
			ty: mir::ValueType::Bool,
		})
	}

	/// The MIR scope a `break` or `continue` targets. A jump only names a
	/// scope that encloses it, and lowering registers a scope before its
	/// body, so the target is already known; a miss would mean the checked
	/// tables disagree and is diagnosed rather than indexed blindly.
	fn jump_scope(
		&mut self,
		body: &Body,
		state: &FunctionState,
		scope: ScopeIdx,
	) -> Result<mir::ScopeIndex, ()> {
		match state.scope_map.get(&scope) {
			Some(&index) => Ok(index),
			None => {
				self.unsupported(
					state.file_id,
					body.scope(scope).span,
					"a jump to a scope that was not lowered",
				)?;
				unreachable!()
			}
		}
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
			// Unreachable from `lower_expr`: `&&`/`||` are lowered as
			// `IfElse` branches (see `lower_short_circuit`). The mapping
			// remains for the exhaustive operator table and hand-built MIR.
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
		let ty = self.normalize_type(ty, env, file_id, span)?;
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

	fn normalize_type(&mut self, ty: TypeIndex, env: TypeEnvIdx, file_id: FileId, span: TextSpan) -> Result<TypeIndex, ()> {
		match self.context.normalize(env, ty, NormalizationDepth::Deep, RewriteFlags::ALL) {
			Ok(ty) => Ok(ty),
			Err(_) => { self.unsupported(file_id, span, "a type that does not normalize")?; unreachable!() }
		}
	}

	/// Materialize one concrete type's flat representation, without a second
	/// structural interner. Memory layout is copied from TIR when available.
	fn lower_aggregate_type(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		if let Some(representation) = self.aggregate_types.get(&ty) {
			return Ok(representation.ty);
		}

		let field_types = self.aggregate_field_types(ty, env, file_id, span)?;
		let mut scalars = Vec::new();
		let mut fields = Vec::with_capacity(field_types.len());
		for field in field_types {
			let field = self.lower_type(field, env, file_id, span)?;
			let start = scalars.len();
			match field {
				mir::ValueType::Unit => {}
				mir::ValueType::Never => { self.unsupported(file_id, span, "an uninhabited aggregate value")?; }
				mir::ValueType::Aggregate { aggregate_index } => scalars.extend_from_slice(&self.aggregates.get(aggregate_index).scalars),
				scalar => scalars.push(scalar),
			}
			fields.push(mir::ScalarRange::new(start.try_into().unwrap(), (scalars.len() - start).try_into().unwrap()));
		}

		let lowered = if scalars.is_empty() {
			mir::ValueType::Unit
		} else {
			let memory = match self.context.memory_values(env, ty) {
				Ok(Some((layout, values))) => {
					assert_eq!(values.len(), scalars.len(), "TIR stack and memory slot counts agree");
					Some(mir::AggregateMemory {
						layout: mir::Layout { size: layout.size, align: layout.align },
						offsets: values.iter().map(|&(_, offset)| offset).collect(),
					})
				}
				Ok(None) => None,
				Err(_) => { self.unsupported(file_id, span, "an aggregate whose memory layout failed")?; unreachable!() }
			};
			let aggregate_index = self.aggregates.push(scalars.into_boxed_slice(), memory);
			mir::ValueType::Aggregate { aggregate_index }
		};
		self.aggregate_types.insert(ty, AggregateLowering { ty: lowered, fields: fields.into_boxed_slice() });
		Ok(lowered)
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
		let ty = self.normalize_type(ty, env, file_id, span)?;
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
	fn std_trap_lowers_to_unreachable_without_a_function_or_call_edge() {
		let source = r#"
			use std::trap as stop;
			func fail() -> ! { stop() }
			export { fail as "fail" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).expect("trap must expand");
		assert_eq!(mir.functions.len(), 1);
		assert!(mir.call_edges.is_empty());
		assert!(mir.imports.is_empty());
		let mir::ExprKind::Block { expressions, .. } =
			&mir.functions[0].block.kind
		else {
			panic!("expected a block")
		};
		assert!(matches!(
			expressions.last().unwrap().kind,
			mir::ExprKind::Unreachable
		));
		let (mut store, instance) = instantiate(source);
		let fail = instance
			.get_typed_func::<(), ()>(&mut store, "fail")
			.unwrap();
		assert!(fail.call(&mut store, ()).is_err());
	}

	#[test]
	fn scalar_intrinsics_expand_by_identity_and_preserve_operand_types() {
		let source = r#"
			use std::i32_add as sum;
			func i32_add(a: i32, b: i32) -> i32 { a - b }
			func run() -> i32 { sum(20, 22) + i32_add(10, 3) }
			func unsigned(a: u32, b: u32) -> u32 { std::u32_div(a, b) }
			func compare(a: u32, b: u32) -> Bool { std::u32_lt(a, b) }
			func convert(x: u32) -> f64 { std::f64_sqrt(std::f64_convert_u32(x)) }
			func bits(x: f32) -> i32 { std::i32_reinterpret_f32(x) }
			export { run as "run", unsigned as "unsigned", compare as "compare", convert as "convert", bits as "bits" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph)
			.expect("scalar intrinsics must expand");
		assert_eq!(
			mir.functions.len(),
			6,
			"only the ordinary callee gets a body"
		);
		assert_eq!(mir.call_edges.len(), 1);
		assert!(mir.imports.is_empty());
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			49
		);
		assert_eq!(
			instance
				.get_typed_func::<(u32, u32), u32>(&mut store, "unsigned")
				.unwrap()
				.call(&mut store, (u32::MAX, 2))
				.unwrap(),
			u32::MAX / 2
		);
		assert_eq!(
			instance
				.get_typed_func::<(u32, u32), i32>(&mut store, "compare")
				.unwrap()
				.call(&mut store, (u32::MAX, 1))
				.unwrap(),
			0
		);
		assert_eq!(
			instance
				.get_typed_func::<u32, f64>(&mut store, "convert")
				.unwrap()
				.call(&mut store, 81)
				.unwrap(),
			9.0
		);
		assert_eq!(
			instance
				.get_typed_func::<f32, i32>(&mut store, "bits")
				.unwrap()
				.call(&mut store, -0.0)
				.unwrap(),
			i32::MIN
		);
	}

	#[test]
	fn split_scalar_intrinsics_preserve_width_and_signedness() {
		let source = r#"
			func signed32(a: i32, b: i32) -> (i32, i32, i32, Bool) {
				(std::i32_div(a, b), std::i32_rem(a, b), std::i32_shr(a, 1), std::i32_lt(a, b))
			}
			func unsigned32(a: u32, b: u32) -> (u32, u32, u32, Bool) {
				(std::u32_div(a, b), std::u32_rem(a, b), std::u32_shr(a, 1), std::u32_lt(a, b))
			}
			func signed64(a: i64, b: i64) -> (i64, i64, i64, Bool) {
				(std::i64_div(a, b), std::i64_rem(a, b), std::i64_shr(a, 1), std::i64_lt(a, b))
			}
			func unsigned64(a: u64, b: u64) -> (u64, u64, u64, Bool) {
				(std::u64_div(a, b), std::u64_rem(a, b), std::u64_shr(a, 1), std::u64_lt(a, b))
			}
			func multiply(a: i32, b: i64, c: f32, d: f64) -> (i32, i64, f32, f64) {
				(std::i32_mul(a, 3), std::i64_mul(b, 3), std::f32_div(std::f32_mul(c, 3), 2), std::f64_div(std::f64_mul(d, 3), 2))
			}
			export { signed32 as "signed32", unsigned32 as "unsigned32", signed64 as "signed64", unsigned64 as "unsigned64", multiply as "multiply" }
		"#;
		let (mut store, instance) = instantiate(source);
		let signed32 = instance
			.get_typed_func::<(i32, i32), (i32, i32, i32, i32)>(
				&mut store, "signed32",
			)
			.unwrap();
		assert_eq!(
			signed32.call(&mut store, (-9, 2)).unwrap(),
			(-4, -1, -5, 1)
		);
		let unsigned32 = instance
			.get_typed_func::<(u32, u32), (u32, u32, u32, i32)>(
				&mut store,
				"unsigned32",
			)
			.unwrap();
		let high32 = (-9i32) as u32;
		assert_eq!(
			unsigned32.call(&mut store, (high32, 2)).unwrap(),
			(high32 / 2, 1, high32 >> 1, 0)
		);
		let signed64 = instance
			.get_typed_func::<(i64, i64), (i64, i64, i64, i32)>(
				&mut store, "signed64",
			)
			.unwrap();
		assert_eq!(
			signed64.call(&mut store, (-9, 2)).unwrap(),
			(-4, -1, -5, 1)
		);
		let unsigned64 = instance
			.get_typed_func::<(u64, u64), (u64, u64, u64, i32)>(
				&mut store,
				"unsigned64",
			)
			.unwrap();
		let high64 = (-9i64) as u64;
		assert_eq!(
			unsigned64.call(&mut store, (high64, 2)).unwrap(),
			(high64 / 2, 1, high64 >> 1, 0)
		);
		let multiply = instance
			.get_typed_func::<(i32, i64, f32, f64), (i32, i64, f32, f64)>(
				&mut store, "multiply",
			)
			.unwrap();
		assert_eq!(
			multiply.call(&mut store, (7, 7, 7.0, 7.0)).unwrap(),
			(21, 21, 10.5, 10.5)
		);
	}

	#[test]
	fn named_intrinsic_and_ordinary_arguments_execute_in_written_order_once() {
		let source = r#"
			func subtract(a: i32, b: i32) -> i32 { a - b }
			func run() -> i32 {
				local mut x: i32 = 0
				local a: i32 = std::i32_sub({
					b: block { x = x + 1; x },
					a: block { x = x + 1; x },
				})
				local b: i32 = subtract({
					b: block { x = x + 1; x },
					a: block { x = x + 1; x },
				})
				a * 100 + b * 10 + x
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 114);
	}

	#[test]
	fn argument_spills_preserve_zero_sized_field_effects() {
		let source = r#"
			struct Value(a: i32, marker: (), b: i32);
			func run() -> i32 {
				local mut x: i32 = 0
				local p: Value = Value({
					b: block { x = x + 1; x },
					marker: block { x = x + 1; () },
					a: block { x = x + 1; x },
				})
				p.a * 100 + p.b * 10 + x
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 313);
	}

	#[test]
	fn intrinsics_accept_computed_argument_tuples_and_diverging_arguments() {
		let source = r#"
			func pair(x: i32) -> (i32, i32) { (x, 2) }
			func run(x: i32) -> i32 { std::i32_sub(pair(x)) }
			func operand() -> i32 { std::i32_add(1, std::trap()) }
			export { run as "run", operand as "operand" }
		"#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<i32, i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, 12)
				.unwrap(),
			10
		);
		assert!(
			instance
				.get_typed_func::<(), i32>(&mut store, "operand")
				.unwrap()
				.call(&mut store, ())
				.is_err()
		);
	}

	#[test]
	fn unavailable_function_implementations_are_explicit_diagnostics() {
		for (source, message) in [
			(
				r#"crate func trap() -> !; func run() -> ! { trap() } export { run as "run" }"#,
				"unfulfilled package function",
			),
			(
				r#"func trap() -> !; func run() -> ! { trap() } export { run as "run" }"#,
				"without an implementation",
			),
			(
				r#"import "env" as host { func trap() -> !; } func run() -> ! { host::trap() } export { run as "run" }"#,
				"imported function",
			),
			(
				r#"use std::trap as provided; export { provided as "trap" }"#,
				"requires a wrapper",
			),
			(
				r#"memory heap: u32; func run() -> u32 { std::size_of::<i32, heap>() } export { run as "run" }"#,
				"compiler intrinsic SizeOf",
			),
		] {
			let mut graph = crate::tir::signatures::tests::source_graph(source);
			let diagnostics = match crate::tir::build(&mut graph) {
				Ok(_) => panic!("unsupported implementation must not emit MIR"),
				Err(diagnostics) => diagnostics,
			};
			assert!(
				diagnostics.iter().any(|d| d.message.contains(message)
					&& d.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code())
					&& !d.labels.is_empty()),
				"expected {message:?}, got {diagnostics:#?}"
			);
		}
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
	fn reports_an_aggregate_constant_pattern_as_an_eq_violation() {
		let source = r#"
            struct Pair(a: i32, b: i32);
            const ORIGIN: Pair = Pair(0, 0);
            func pick(p: Pair) -> i32 {
                match p {
                    const ORIGIN => { 1 },
                    _ => { 2 },
                }
            }
            export { pick as "pick" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let diagnostics = match crate::tir::build(&mut graph) {
			Ok(_) => panic!("an aggregate constant pattern has no equality"),
			Err(diagnostics) => diagnostics,
		};
		assert!(
			diagnostics.iter().any(|d| {
				d.message.contains("`Pair: Eq` is not satisfied")
					&& d.code.as_deref()
						== Some(DiagnosticCode::TraitBoundViolation.code())
			}),
			"expected an Eq trait-bound diagnostic, got {diagnostics:#?}"
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
	fn nested_fields_are_flat_ranges_for_reads_and_updates() {
		let source = r#"
			struct Inner(a: i32, marker: (), b: i64);
			struct Outer(marker: (), inner: Inner, c: i32);
			func run() -> (i32, i64, i32) {
				local mut x: i32 = 0
				local mut o: Outer = Outer((), Inner(1, (), 2), 3)
				o.inner = Inner(4, (), 5)
				o.inner.b = 99
				o.inner.marker = block { x = x + 1; () }
				_ = o.inner.marker;
				(o.inner.a + x, o.inner.b, o.c)
			}
			export { run as "run" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).expect("nested updates must lower");
		assert!(mir.aggregates.iter().all(|pack| pack.scalars.iter().all(|ty| !matches!(ty, mir::ValueType::Aggregate { .. } | mir::ValueType::Unit | mir::ValueType::Never))));
		let (mut store, instance) = instantiate(source);
		let run = instance.get_typed_func::<(), (i32, i64, i32)>(&mut store, "run").unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), (5, 99, 3));
	}

	#[test]
	fn equal_memory_layouts_do_not_confuse_source_projection_shapes() {
		let source = r#"
			struct Wrapper(value: i32);
			struct Nested(x: Wrapper, y: i32);
			struct Plain(x: i32, y: i32);
			func nested(n: Nested) -> i32 { n.x.value + n.y }
			func plain(p: Plain) -> i32 { p.x + p.y }
			func run() -> (i32, i32) { (nested(Nested(Wrapper(3), 4)), plain(Plain(5, 6))) }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance.get_typed_func::<(), (i32, i32)>(&mut store, "run").unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), (7, 11));
	}

	#[test]
	fn same_slot_types_with_distinct_layouts_coexist_in_one_module() {
		let source = r#"
			struct Sorted(a: u8, b: i64, c: u8);
			#[fixed_order]
			struct Fixed(a: u8, b: i64, c: u8);
			func sorted(x: Sorted) -> Sorted { x }
			func fixed(x: Fixed) -> Fixed { x }
			export { sorted as "sorted", fixed as "fixed" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).unwrap();
		let layouts: Vec<_> = mir.aggregates.iter().map(|pack| {
			assert_eq!(pack.scalars.as_ref(), [mir::ValueType::U8, mir::ValueType::I64, mir::ValueType::U8]);
			pack.memory.as_ref().unwrap().offsets.to_vec()
		}).collect();
		assert!(layouts.contains(&vec![8, 0, 9]));
		assert!(layouts.contains(&vec![0, 8, 16]));
		let (mut store, instance) = instantiate(source);
		for name in ["sorted", "fixed"] {
			let identity = instance.get_typed_func::<(i32, i64, i32), (i32, i64, i32)>(&mut store, name).unwrap();
			assert_eq!(identity.call(&mut store, (7, 1 << 40, 9)).unwrap(), (7, 1 << 40, 9));
		}
	}

	#[test]
	fn computed_argument_tuples_preserve_subpack_and_zero_sized_parameters() {
		let source = r#"
			struct Pair(a: i32, b: i32);
			func args(x: i32) -> (Pair, (), i32) { (Pair(x, 2), (), 3) }
			func sum(p: Pair, marker: (), c: i32) -> i32 { p.a + p.b + c }
			func units() -> ((), ()) { ((), ()) }
			func empty(a: (), b: ()) -> i32 { 7 }
			func run() -> i32 { sum(args(10)) + empty(units()) }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance.get_typed_func::<(), i32>(&mut store, "run").unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 22);
	}

	#[test]
	fn erased_zero_sized_values_still_execute_calls_and_can_trap() {
		for source in [
			r#"struct Zero(marker: ()); func fail() { std::trap() } func run() -> i32 { local z: Zero = Zero(fail()); _ = z; 7 } export { run as "run" }"#,
			r#"struct Zero(marker: ()); func fail() { std::trap() } func run() -> i32 { local mut z: Zero = Zero(()); z.marker = fail(); 7 } export { run as "run" }"#,
			r#"struct Zero(); func make() -> Zero { std::trap() } func run() -> i32 { _ = make(); 7 } export { run as "run" }"#,
		] {
			let (mut store, instance) = instantiate(source);
			let run = instance.get_typed_func::<(), i32>(&mut store, "run").unwrap();
			assert!(run.call(&mut store, ()).is_err());
		}
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
				aggregate.scalars.iter().copied().eq([
					mir::ValueType::U8,
					mir::ValueType::I64,
					mir::ValueType::U8,
				])
			})
			.expect("the struct's aggregate must be interned");
		let offsets = aggregate.memory.as_ref().unwrap().offsets.to_vec();
		assert_eq!(offsets, vec![8, 0, 9], "TIR decides the byte offsets");

		let scalar_types = aggregate.scalars.to_vec();
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

	/// A tuple `local` pattern projects its elements from the value; a local
	/// initializer is read in place rather than copied first.
	#[test]
	fn destructures_a_tuple_local_from_a_parameter() {
		let source = r#"
            func run(pair: (i32, i32)) -> i32 {
                local (a, b) = pair
                a * 10 + b
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (1, 2)).unwrap(), 12);
	}

	/// A structural `local` pattern spills a non-local initializer once and
	/// binds its fields from the temporary.
	#[test]
	fn destructures_a_struct_local_from_a_call() {
		let source = r#"
            struct Pair(a: i32, b: i32);
            struct Outer(pair: Pair, c: i32);
            func make() -> Outer { Outer(Pair(1, 2), 3) }
            func run() -> i32 {
                local Outer(Pair(a, _), c) = make()
                a * 10 + c
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 13);
	}

	/// A named struct pattern binds its fields in declaration order whatever
	/// names the pattern gives them.
	#[test]
	fn destructures_a_named_struct_local_with_field_renames() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func run() -> i32 {
                local Point({ x: a, y: b }) = Point({ x: 1, y: 2 })
                a * 10 + b
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 12);
	}

	/// Rest elements and zero-sized fields bind nothing and occupy no slot.
	#[test]
	fn destructures_nested_rest_and_zero_sized_local_fields() {
		let source = r#"
            struct Marker();
            struct Pair(a: i32, b: i32);
            struct Outer(pair: Pair, marker: Marker, c: i32);
            func run() -> i32 {
                local Outer(Pair(a, ..), .., c) = Outer(Pair(3, 2), Marker(), 4)
                a * 10 + c
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 34);
	}

	/// A local `|` pattern is irrefutable, so its first alternative binds.
	#[test]
	fn an_irrefutable_or_local_pattern_binds_its_first_alternative() {
		let source = r#"
            func run(pair: (i32, i32)) -> i32 {
                local (a, b) | (a, b) = pair
                a * 10 + b
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (5, 6)).unwrap(), 56);
	}

	/// A destructuring initializer that diverges never binds anything.
	#[test]
	fn a_diverging_destructuring_initializer_is_unreachable() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 {
                local (a, b): (i32, i32) = stop()
                a + b
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// Primitive compound assignment reads the target, applies the operator,
	/// and stores the result back.
	#[test]
	fn lowers_primitive_compound_assignment() {
		let source = r#"
            func run() -> i32 {
                local mut x: i32 = 1
                x += 2
                x *= 3
                x <<= 1
                x -= 4
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 14);
	}

	/// A nested field is projected to its flat slot range, updated there,
	/// and leaves the surrounding aggregate intact.
	#[test]
	fn compound_assignment_updates_a_nested_field_in_place() {
		let source = r#"
            struct Inner(a: i32, marker: (), b: i64);
            struct Outer(marker: (), inner: Inner, c: i32);
            func run() -> (i32, i64, i32) {
                local mut o: Outer = Outer((), Inner(1, (), 2), 3)
                o.inner.a += 4;
                o.inner.b *= 7;
                o.c += 2;
                (o.inner.a, o.inner.b, o.c)
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), (i32, i64, i32)>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), (5, 14, 5));
	}

	/// A concrete operator impl lowers to a direct call whose receiver is the
	/// target's current value and whose result is stored back.
	#[test]
	fn compound_assignment_through_a_concrete_operator_impl() {
		let source = r#"
            struct Total(value: i32);
            impl Add for Total {
                func add(self: Self, rhs: Self) -> Self {
                    Total(self.value + rhs.value)
                }
            }
            func run() -> i32 {
                local mut total = Total(1)
                total += Total(2)
                total.value
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 3);
	}

	/// A concrete compound assignment also evaluates its operand before
	/// reading the receiver target.
	#[test]
	fn a_concrete_compound_operand_runs_before_the_target_read() {
		let source = r#"
            struct Total(value: i32);
            impl Add for Total {
                func add(self: Self, rhs: Self) -> Self {
                    Total(self.value + rhs.value)
                }
            }
            func run() -> i32 {
                local mut total = Total(1)
                total += block { total = Total(10); Total(2) }
                total.value
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 12);
	}

	/// `target = target op value` evaluates the operand first, then reads
	/// the target. The operand can therefore overwrite the target before the
	/// read that the operator uses.
	#[test]
	fn a_compound_operand_runs_before_the_target_read() {
		let source = r#"
            func run() -> i32 {
                local mut x: i32 = 1
                x += block { x = 10; 2 }
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 12);
	}

	/// The operand still goes on the operator's right, so a non-commutative
	/// operator is not accidentally reversed when it is evaluated first.
	#[test]
	fn a_compound_operand_keeps_the_operator_order() {
		let source = r#"
            func run() -> i32 {
                local mut x: i32 = 1
                x -= block { x = 10; 2 }
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 8);
	}

	/// A diverging operand prevents the store and leaves the whole statement
	/// unreachable.
	#[test]
	fn a_diverging_compound_operand_is_unreachable() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 {
                local mut x: i32 = 1
                x += stop()
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
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

	/// A call whose argument diverges never reaches the callee. The optimizer
	/// must stop at the argument's `unreachable` instead of materializing a
	/// value for it.
	#[test]
	fn a_diverging_call_argument_makes_the_call_unreachable() {
		let source = r#"
            use std::trap as stop;
            func identity(x: i32) -> i32 { x }
            func run() -> i32 { identity(stop()) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// A call whose declared result is `!` runs for its effects but never
	/// hands control back. The caller must be terminated rather than falling
	/// through as if the call were a unit expression.
	#[test]
	fn a_call_to_a_diverging_function_never_returns() {
		let source = r#"
            use std::trap as stop;
            func fail() -> ! { stop() }
            func run() -> i32 { fail() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// Divergence propagates out of both operand positions, and the operand
	/// written first is the one evaluated first.
	#[test]
	fn a_diverging_binary_operand_makes_the_operation_unreachable() {
		let source = r#"
            use std::trap as stop;
            func left(x: i32) -> i32 { stop() + x }
            func right(x: i32) -> i32 { x + stop() }
            func both(x: i32) -> i32 { stop() + stop() }
            export { left as "left", right as "right", both as "both" }
        "#;
		let (mut store, instance) = instantiate(source);
		for name in ["left", "right", "both"] {
			let run = instance
				.get_typed_func::<i32, i32>(&mut store, name)
				.unwrap_or_else(|_| panic!("`{name}` must be exported"));
			assert!(run.call(&mut store, 0).is_err(), "{name}");
		}
	}

	/// A diverging unary operand makes the unary expression unreachable in
	/// either the arithmetic or the logical form.
	#[test]
	fn a_diverging_unary_operand_makes_the_operation_unreachable() {
		let source = r#"
            use std::trap as stop;
            func negate(x: i32) -> i32 { -stop() }
            func logical(x: Bool) -> Bool { !stop() }
            export { negate as "negate", logical as "logical" }
        "#;
		let (mut store, instance) = instantiate(source);
		for name in ["negate", "logical"] {
			let run = instance
				.get_typed_func::<i32, i32>(&mut store, name)
				.unwrap_or_else(|_| panic!("`{name}` must be exported"));
			assert!(run.call(&mut store, 0).is_err(), "{name}");
		}
	}

	/// A diverging initializer leaves its local unbound and the rest of the
	/// block unreachable.
	#[test]
	fn a_diverging_local_initializer_is_unreachable() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 {
                local x = stop()
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// Dropping a diverging value is still divergence; the drop itself does
	/// not turn the expression into a unit value.
	#[test]
	fn a_diverging_drop_is_unreachable() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 {
                _ = stop()
                7
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// A diverging statement makes the rest of the body unreachable even
	/// when a later expression gives the block a non-`Never` type. The
	/// function still needs an explicit terminator after the divergence.
	#[test]
	fn a_diverging_statement_before_a_result_still_terminates_the_body() {
		let source = r#"
            use std::trap as stop;
            func fail() -> ! { stop() }
            func run() -> i32 { fail(); 1 }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// A return whose value diverges never performs the return.
	#[test]
	fn a_diverging_return_value_is_unreachable() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 { return stop() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	// ── loops, breaks, continues and labelled blocks ──────────────────────

	/// A loop leaves through its `break`, carrying the value it gives.
	#[test]
	fn a_loop_break_carries_the_loop_result() {
		let source = r#"
            func run() -> i32 { loop { break 42; } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.expect("`run` must be exported")
				.call(&mut store, ())
				.unwrap(),
			42
		);
	}

	/// A bare `break` gives the loop the unit value.
	#[test]
	fn a_bare_break_leaves_the_loop_with_unit() {
		let source = r#"
            func run() { loop { break; } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		instance
			.get_typed_func::<(), ()>(&mut store, "run")
			.expect("`run` must be exported")
			.call(&mut store, ())
			.unwrap();
	}

	/// A loop result is an ordinary value: it initializes a local like any
	/// other expression.
	#[test]
	fn a_loop_result_initializes_a_local() {
		let source = r#"
            func run() -> i32 {
                local n: i32 = loop { break 3; };
                n + 1
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			4
		);
	}

	/// Each loop owns its scope: an unlabelled break leaves the innermost
	/// loop, not any outer one.
	#[test]
	fn nested_loops_break_their_own_scopes() {
		let source = r#"
            func run() -> i32 {
                loop {
                    loop { break; }
                    break 7;
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			7
		);
	}

	/// A labelled break can leave an outer loop from an inner one.
	#[test]
	fn a_labelled_break_leaves_the_named_outer_loop() {
		let source = r#"
            func run() -> i32 {
                loop :outer {
                    loop {
                        break :outer 8;
                    }
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			8
		);
	}

	/// A labelled block is a break target of its own; its value comes from
	/// the break, not from falling off the end.
	#[test]
	fn a_labelled_block_takes_its_value_from_break() {
		let source = r#"
            func run() -> i32 {
                block :done { break :done 9; }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			9
		);
	}

	/// A labelled block that simply falls through still yields its last
	/// expression: its label does not create a join by itself.
	#[test]
	fn a_labelled_block_falls_through_like_any_block() {
		let source = r#"
            func run() -> i32 {
                block :done { 6 }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			6
		);
	}

	/// A break inside a loop can leave an enclosing labelled block instead
	/// of the loop, skipping the rest of the loop body.
	#[test]
	fn a_break_can_leave_a_loop_for_an_enclosing_labelled_block() {
		let source = r#"
            func run() -> i32 {
                block :done {
                    loop {
                        break :done 4;
                    }
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			4
		);
	}

	/// A multi-scalar value crosses a loop join like it crosses an `if`'s:
	/// every scalar needs its own carried result.
	#[test]
	fn an_aggregate_break_value_crosses_the_loop_join() {
		let source = r#"
            func run() -> (i32, i32) { loop { break (1, 2); } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), (i32, i32)>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			(1, 2)
		);
	}

	/// An empty loop has no exit at all; it must still encode as valid
	/// Wasm. Instantiating does not run it.
	#[test]
	fn an_empty_loop_encodes() {
		let source = r#"
            func run() -> ! { loop {} }
            export { run as "run" }
        "#;
		let _ = instantiate(source);
	}

	// ── constants ────────────────────────────────────────────────────────

	/// `True` and `False` are `Bool`'s variants, and a `const` of that type
	/// reads the same way.
	#[test]
	fn bool_literals_and_constants_lower() {
		let source = r#"
            const YES: Bool = True;
            func yes() -> Bool { True }
            func no() -> Bool { False }
            func named() -> Bool { YES }
            export { yes as "yes", no as "no", named as "named" }
        "#;
		let (mut store, instance) = instantiate(source);
		for (name, expected) in [("yes", 1), ("no", 0), ("named", 1)] {
			let run = instance
				.get_typed_func::<(), i32>(&mut store, name)
				.unwrap_or_else(|_| panic!("`{name}` must be exported"));
			assert_eq!(run.call(&mut store, ()).unwrap(), expected, "{name}");
		}
	}

	/// A constant keeps the checked width, signedness and float precision,
	/// including values that do not fit `i64`.
	#[test]
	fn scalar_constants_keep_their_checked_type() {
		let source = r#"
            const TWO: i32 = 2;
            const SIX: i32 = TWO * 3;
            const NEG: i8 = -5;
            const BIG: u64 = 18446744073709551615;
            const HALF: f64 = 0.5;
            const NFLAG: f32 = -1.5;
            func six() -> i32 { SIX }
            func neg() -> i8 { NEG }
            func big() -> u64 { BIG }
            func half() -> f64 { HALF }
            func nflag() -> f32 { NFLAG }
            export {
                six as "six", neg as "neg", big as "big",
                half as "half", nflag as "nflag",
            }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "six")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			6
		);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "neg")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			-5
		);
		assert_eq!(
			instance
				.get_typed_func::<(), u64>(&mut store, "big")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			u64::MAX
		);
		assert_eq!(
			instance
				.get_typed_func::<(), f64>(&mut store, "half")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			0.5
		);
		assert_eq!(
			instance
				.get_typed_func::<(), f32>(&mut store, "nflag")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			-1.5
		);
	}

	/// A variant written without a value counts on from the one before it;
	/// the checker evaluates that when it reads the constant.
	#[test]
	fn enum_variant_constants_include_implicit_discriminants() {
		let source = r#"
            enum Color(u8) { Red = 3, Green, Blue }
            func green() -> Color { Color::Green }
            func blue() -> Color { Color::Blue }
            export { green as "green", blue as "blue" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "green")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			4
		);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "blue")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			5
		);
	}

	/// An aggregate constant is already flat in declaration order; each
	/// scalar becomes its own leaf node and the whole is assembled once.
	#[test]
	fn aggregate_constants_are_assembled_from_flat_scalars() {
		let source = r#"
            struct Point(x: i32, y: i32);
            struct Flags(on: Bool, off: Bool);
            const P: Point = Point(3, 4);
            const F: Flags = Flags(True, False);
            func sum() -> i32 { P.x + P.y }
            func on() -> Bool { F.on }
            func off() -> Bool { F.off }
            export { sum as "sum", on as "on", off as "off" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "sum")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			7
		);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "on")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			1
		);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "off")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			0
		);
	}

	/// Nesting is already flattened in the constant's value, so a nested
	/// aggregate constant assembles in one go too.
	#[test]
	fn a_nested_aggregate_constant_is_flat() {
		let source = r#"
            struct Inner(a: i32, b: i32);
            struct Outer(inner: Inner, c: i32);
            const O: Outer = Outer(Inner(1, 2), 3);
            func run() -> i32 { O.inner.a + O.inner.b + O.c }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			6
		);
	}

	/// A constant is a value wherever any other expression is, including an
	/// `if` condition.
	#[test]
	fn a_bool_constant_drives_control_flow() {
		let source = r#"
            const YES: Bool = True;
            func run() -> i32 { if YES { 1 } else { 2 } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			1
		);
	}

	/// A unit-valued constant has no slots, so it becomes a no-op.
	#[test]
	fn a_unit_constant_is_a_noop() {
		let source = r#"
            const NOTHING: () = ();
            func run() { NOTHING }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		instance
			.get_typed_func::<(), ()>(&mut store, "run")
			.unwrap()
			.call(&mut store, ())
			.unwrap();
	}

	// ── method calls ─────────────────────────────────────────────────────

	/// An inherent method lowers to a direct call whose first argument is
	/// its receiver; the method body itself is lowered as its own function.
	#[test]
	fn an_inherent_method_call_reaches_its_body() {
		let source = r#"
            struct Point(x: i32, y: i32);
            impl Point {
                func sum(self: Self) -> i32 { self.x + self.y }
                func scaled(self: Self, k: i32) -> i32 { self.sum() * k }
            }
            func run() -> i32 { Point(2, 3).scaled(4) }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			20
		);
	}

	/// Named arguments are reordered into the callee's order; the receiver
	/// still runs before the reordered argument evaluations.
	#[test]
	fn named_method_arguments_keep_written_order() {
		let source = r#"
            struct Point(x: i32, y: i32);
            impl Point {
                func combine(self: Self, a: i32, b: i32) -> i32 { a - b }
            }
            func run() -> i32 {
                Point(0, 0).combine({ b: 5, a: 10 })
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			5
		);
	}

	/// A zero-sized receiver occupies no argument slot, even when the
	/// remaining arguments are reordered through temporaries.
	#[test]
	fn a_zero_sized_receiver_survives_argument_reordering() {
		let source = r#"
            struct Marker();
            impl Marker {
                func combine(self: Self, a: i32, b: i32) -> i32 { a - b }
            }
            func run() -> i32 {
                Marker().combine({ b: 2, a: 9 })
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			7
		);
	}

	/// A method may return an aggregate, which is then an ordinary value.
	#[test]
	fn a_method_can_return_an_aggregate() {
		let source = r#"
            struct Point(x: i32, y: i32);
            impl Point {
                func swap(self: Self) -> Point {
                    Point(self.y, self.x)
                }
            }
            func run() -> i32 { Point(1, 2).swap().x }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			2
		);
	}

	/// A concrete trait impl's own method is directly callable, not just
	/// through its operator.
	#[test]
	fn a_trait_impl_method_is_a_direct_call() {
		let source = r#"
            struct P(value: i32);
            impl Add for P {
                func add(self: Self, rhs: Self) -> P {
                    P(self.value + rhs.value)
                }
            }
            func run() -> i32 { P(2).add(P(3)).value }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			5
		);
	}

	/// A std inherent method whose body calls an intrinsic works too.
	#[test]
	fn a_std_method_reaches_its_intrinsic_body() {
		let source = r#"
            func run(x: f32) -> f32 { x.abs() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<f32, f32>(&mut store, "run")
				.unwrap()
				.call(&mut store, -3.5)
				.unwrap(),
			3.5
		);
	}

	/// An enum's inherent method reads its receiver by value.
	#[test]
	fn an_enum_method_call_compares_its_receiver() {
		let source = r#"
            func run() -> Bool { Ordering::Less.is_lt() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		assert_eq!(
			instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap()
				.call(&mut store, ())
				.unwrap(),
			1
		);
	}

	/// A diverging receiver prevents the method from running.
	#[test]
	fn a_diverging_receiver_never_calls_the_method() {
		let source = r#"
            use std::trap as stop;
            struct Point(x: i32, y: i32);
            impl Point {
                func sum(self: Self) -> i32 { self.x + self.y }
            }
            func make() -> Point { stop() }
            func run() -> i32 { make().sum() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	// ── match ────────────────────────────────────────────────────────────
	/// A scalar match with a wildcard lowers to MIR `Switch`; the wildcard
	/// is the default arm, not a case.
	#[test]
	fn a_scalar_match_selects_the_first_matching_arm() {
		let source = r#"
            func run(x: i32) -> i32 {
                match x {
                    0 => { 10 },
                    1 => { 20 },
                    _ => { 30 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 10);
		assert_eq!(run.call(&mut store, 1).unwrap(), 20);
		assert_eq!(run.call(&mut store, 2).unwrap(), 30);
	}

	/// An arm body need not be a block; a bare expression is its value.
	#[test]
	fn a_match_arm_body_may_be_an_expression() {
		let source = r#"
            func run(x: i32) -> i32 {
                match x {
                    0 => 10,
                    1 => { local y: i32 = 20; y },
                    n => n + 1,
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 10);
		assert_eq!(run.call(&mut store, 1).unwrap(), 20);
		assert_eq!(run.call(&mut store, 2).unwrap(), 3);
	}

	/// Every enum variant covered without `_` is exhaustive; there is no
	/// default body and reaching one would be unreachable.
	#[test]
	fn an_exhaustive_enum_match_has_no_default() {
		let source = r#"
            enum Color(u8) { Red = 0, Green, Blue }
            func run(c: Color) -> i32 {
                match c {
                    Color::Red => { 1 },
                    Color::Green => { 2 },
                    Color::Blue => { 3 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
		assert_eq!(run.call(&mut store, 1).unwrap(), 2);
		assert_eq!(run.call(&mut store, 2).unwrap(), 3);
	}

	/// `True` and `False` are constants of the bool enum.
	#[test]
	fn a_bool_match_compares_bool_constants() {
		let source = r#"
            func run(b: Bool) -> i32 {
                match b {
                    const True => { 1 },
                    const False => { 0 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 0);
	}

	/// A binding wildcard needs the scrutinee after the selector was read,
	/// so it is spilled first. The bound enum is used again by a nested
	/// match.
	#[test]
	fn a_binding_default_receives_the_scrutinee() {
		let source = r#"
            enum Color(u8) { Red = 0, Green, Blue }
            func run(c: Color) -> i32 {
                match c {
                    Color::Red => { 1 },
                    other => {
                        match other {
                            Color::Green => { 2 },
                            Color::Blue => { 3 },
                            _ => { 4 },
                        }
                    },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
		assert_eq!(run.call(&mut store, 1).unwrap(), 2);
		assert_eq!(run.call(&mut store, 2).unwrap(), 3);
	}

	/// A tuple pattern projects its elements from the stored scrutinee and
	/// binds only on the matching arm.
	#[test]
	fn a_tuple_match_projects_and_binds() {
		let source = r#"
            func run(a: i32, b: i32) -> i32 {
                local pair = (a, b)
                match pair {
                    (0, y) => { y },
                    (x, _) => { x },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 3);
	}

	/// A positional struct pattern uses the struct's fields as its flat
	/// product; the first arm tests a field, the second is irrefutable.
	#[test]
	fn a_struct_match_projects_and_binds() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func run(a: i32, b: i32) -> i32 {
                local p = Point(a, b)
                match p {
                    Point(0, y) => { y },
                    Point(x, _) => { x },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 3);
	}

	/// A named struct pattern has one child per field in declaration order,
	/// whatever the source wrote.
	#[test]
	fn a_named_struct_match_uses_declaration_order() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func run(a: i32, b: i32) -> i32 {
                local p = Point({ x: a, y: b })
                match p {
                    Point({ x: 0, y }) => { y },
                    Point({ x, .. }) => { x },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 3);
	}

	/// The alternatives of `|` bind the same local, so the binding selector
	/// must pick the alternative that actually matched.
	#[test]
	fn an_or_pattern_selects_the_matching_alternative_binding() {
		let source = r#"
            func run(a: i32, b: i32) -> i32 {
                local pair = (a, b)
                match pair {
                    (0, x) | (x, 1) => { x },
                    _ => { 99 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 1)).unwrap(), 3);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 99);
	}

	/// A nested `|` inside a tuple contributes a disjunction to the arm
	/// condition without losing the structural tests around it.
	#[test]
	fn a_nested_or_pattern_is_a_condition() {
		let source = r#"
            func run(a: i32, b: i32) -> i32 {
                local pair = (a, b)
                match pair {
                    ((0 | 1), y) => { y },
                    _ => { 9 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (1, 6)).unwrap(), 6);
		assert_eq!(run.call(&mut store, (2, 7)).unwrap(), 9);
	}

	/// An aggregate-typed match result crosses the decision tree's joins.
	#[test]
	fn a_match_result_may_be_an_aggregate() {
		let source = r#"
            func run(a: i32) -> (i32, i32) {
                match a {
                    0 => { (1, 2) },
                    _ => { (3, 4) },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, (i32, i32)>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), (1, 2));
		assert_eq!(run.call(&mut store, 1).unwrap(), (3, 4));
	}

	/// A diverging scrutinee prevents every arm from running.
	#[test]
	fn a_diverging_scrutinee_never_matches() {
		let source = r#"
            func make() -> i32 { std::trap() }
            func run() -> i32 {
                match make() {
                    0 => { 1 },
                    _ => { 2 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert!(run.call(&mut store, ()).is_err());
	}

	/// A diverging arm does not disturb the other arms' joins.
	#[test]
	fn a_diverging_arm_does_not_change_the_other_results() {
		let source = r#"
            func run(x: i32) -> i32 {
                match x {
                    0 => { std::trap() },
                    _ => { 7 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert!(run.call(&mut store, 0).is_err());
		assert_eq!(run.call(&mut store, 1).unwrap(), 7);
	}

	/// A duplicate scalar case is unreachable; the earlier arm wins even on
	/// the `br_table` path, where duplicate discriminants would otherwise
	/// map to the later body.
	#[test]
	fn a_duplicate_case_keeps_the_first_arm() {
		let source = r#"
            func run(x: i32) -> i32 {
                match x {
                    0 => { 1 },
                    0 => { 2 },
                    1 => { 3 },
                    _ => { 4 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
		assert_eq!(run.call(&mut store, 1).unwrap(), 3);
		assert_eq!(run.call(&mut store, 2).unwrap(), 4);
	}

	/// Enum variants with a signed narrow representation keep their
	/// negative discriminants through the constant query.
	#[test]
	fn an_enum_with_negative_discriminants_matches() {
		let source = r#"
            enum Sign(i8) { Neg = -1, Zero = 0, Pos = 1 }
            func run(s: Sign) -> i32 {
                match s {
                    Sign::Neg => { 1 },
                    Sign::Zero => { 2 },
                    Sign::Pos => { 3 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, -1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
		assert_eq!(run.call(&mut store, 1).unwrap(), 3);
	}

	/// Narrow signed pattern bits are sign-extended before comparing with a
	/// runtime value.
	#[test]
	fn narrow_signed_patterns_compare_with_sign_extension() {
		let source = r#"
            func run(x: i8) -> i32 {
                match x {
                    -1 => { 1 },
                    0 => { 2 },
                    1 => { 3 },
                    _ => { 4 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, -1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
		assert_eq!(run.call(&mut store, 1).unwrap(), 3);
		assert_eq!(run.call(&mut store, 5).unwrap(), 4);
	}

	/// A free constant is a scalar pattern; it needs `const` so the parser
	/// does not read the name as a binding.
	#[test]
	fn a_free_constant_is_a_scalar_pattern() {
		let source = r#"
            const ZERO: i32 = 0;
            func run(x: i32) -> i32 {
                match x {
                    const ZERO => { 1 },
                    _ => { 2 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
		assert_eq!(run.call(&mut store, 1).unwrap(), 2);
	}

	/// A char pattern compares the codepoint field of the `Char` struct.
	#[test]
	fn a_char_match_compares_codepoints() {
		let source = r#"
            func run(c: Char) -> i32 {
                match c {
                    'a' => { 1 },
                    'b' => { 2 },
                    _ => { 3 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 'a' as i32).unwrap(), 1);
		assert_eq!(run.call(&mut store, 'b' as i32).unwrap(), 2);
		assert_eq!(run.call(&mut store, 'z' as i32).unwrap(), 3);
	}

	/// A named `Char` constant is an aggregate value. Matching it calls the
	/// `PartialEq` impl that `Eq` requires, just like `==` does.
	#[test]
	fn a_named_char_constant_matches_through_eq() {
		let source = r#"
            const A: Char = 'a';
            const B: Char = 'b';
            func run(c: Char) -> i32 {
                match c {
                    const A => 1,
                    const B => 2,
                    _ => 3,
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 'a' as i32).unwrap(), 1);
		assert_eq!(run.call(&mut store, 'b' as i32).unwrap(), 2);
		assert_eq!(run.call(&mut store, 'z' as i32).unwrap(), 3);
	}

	/// An aggregate constant pattern dispatches to the type's own `Eq` impl,
	/// not to a field-by-field comparison. Here `10` equals `20` because the
	/// impl compares only the last digit.
	#[test]
	fn an_aggregate_constant_pattern_uses_the_types_equality() {
		let source = r#"
            struct P(x: i32);
            impl PartialEq for P {
                func eq(self: Self, other: Self) -> Bool {
                    self.x % 10 == other.x % 10
                }
            }
            impl Eq for P {}
            const TEN: P = P(10);
            func run(p: P) -> i32 {
                match p {
                    const TEN => 1,
                    _ => 2,
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 20).unwrap(), 1);
		assert_eq!(run.call(&mut store, 21).unwrap(), 2);
	}

	/// A multi-scalar aggregate constant is materialized flat and passed to
	/// the equality method as one aggregate argument.
	#[test]
	fn a_multi_field_aggregate_constant_matches_through_eq() {
		let source = r#"
            struct Pair(a: i32, b: i32);
            impl PartialEq for Pair {
                func eq(self: Self, other: Self) -> Bool {
                    self.a == other.a && self.b == other.b
                }
            }
            impl Eq for Pair {}
            const ORIGIN: Pair = Pair(0, 0);
            func run(p: Pair) -> i32 {
                match p {
                    const ORIGIN => 1,
                    _ => 2,
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 1);
		assert_eq!(run.call(&mut store, (0, 1)).unwrap(), 2);
	}

	/// An aggregate constant nested in a structural pattern compares the
	/// projected field through its own equality.
	#[test]
	fn a_nested_aggregate_constant_compares_its_projection() {
		let source = r#"
            struct Wrapper(value: Char);
            const A: Char = 'a';
            func run(c: Char) -> i32 {
                local w = Wrapper(c)
                match w {
                    Wrapper(const A) => 1,
                    Wrapper(_) => 2,
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 'a' as i32).unwrap(), 1);
		assert_eq!(run.call(&mut store, 'b' as i32).unwrap(), 2);
	}

	/// A char pattern nested in a struct projects through the field to the
	/// codepoint.
	#[test]
	fn a_nested_char_pattern_projects_to_the_codepoint() {
		let source = r#"
            struct Wrapper(value: Char);
            func run(c: Char) -> i32 {
                local w = Wrapper(c)
                match w {
                    Wrapper('a') => { 1 },
                    Wrapper(_) => { 2 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 'a' as i32).unwrap(), 1);
		assert_eq!(run.call(&mut store, 'b' as i32).unwrap(), 2);
	}

	/// A character literal materializes the one-scalar `Char` aggregate.
	#[test]
	fn a_char_literal_materializes_its_codepoint() {
		let source = r#"
            func run() -> Char { 'a' }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 'a' as i32);
	}

	/// A `()` scrutinee has no slots; the match still evaluates it and runs
	/// its irrefutable arm.
	#[test]
	fn a_unit_scrutinee_matches_its_arm() {
		let source = r#"
            func run() -> i32 {
                match () {
                    _ => { 5 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 5);
	}

	/// A character literal coerces to an integer its codepoint fits.
	#[test]
	fn a_character_literal_can_coerce_to_an_integer() {
		let source = r#"
            func wide() -> u32 { 'a' }
            func narrow() -> i8 { 'b' }
            export { wide as "wide", narrow as "narrow" }
        "#;
		let (mut store, instance) = instantiate(source);
		let wide = instance
			.get_typed_func::<(), i32>(&mut store, "wide")
			.unwrap();
		assert_eq!(wide.call(&mut store, ()).unwrap(), 'a' as i32);
		let narrow = instance
			.get_typed_func::<(), i32>(&mut store, "narrow")
			.unwrap();
		assert_eq!(narrow.call(&mut store, ()).unwrap(), 'b' as i32);
	}

	/// A zero-sized struct pattern is irrefutable and binds nothing.
	#[test]
	fn a_zero_sized_struct_pattern_is_irrefutable() {
		let source = r#"
            struct Marker();
            func run() -> i32 {
                local m = Marker()
                match m {
                    Marker() => { 7 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 7);
	}

	/// A non-local aggregate scrutinee is evaluated once into a temporary
	/// before any field test reads it.
	#[test]
	fn a_non_local_aggregate_scrutinee_is_spilled_once() {
		let source = r#"
            struct Point(x: i32, y: i32);
            func make(a: i32, b: i32) -> Point { Point(a, b) }
            func run(a: i32, b: i32) -> i32 {
                match make(a, b) {
                    Point(0, y) => { y },
                    Point(x, _) => { x },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 3);
	}

	/// A one-field named struct pattern matches its field's own type, not a
	/// tuple of one.
	#[test]
	fn a_one_field_named_struct_match_projects_the_field() {
		let source = r#"
            struct Wrapper(value: i32);
            func run(a: i32) -> i32 {
                local w = Wrapper({ value: a })
                match w {
                    Wrapper({ value: 0 }) => { 1 },
                    Wrapper({ value }) => { value },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
		assert_eq!(run.call(&mut store, 7).unwrap(), 7);
	}

	/// A one-field aggregate field is retyped as that field's aggregate,
	/// preserving the scalar layout.
	#[test]
	fn a_one_field_aggregate_match_projects_nested_fields() {
		let source = r#"
            struct Pair(a: i32, b: i32);
            struct Holder(pair: Pair);
            func run(a: i32, b: i32) -> i32 {
                local h = Holder({ pair: Pair(a, b) })
                match h {
                    Holder({ pair: Pair(0, y) }) => { y },
                    Holder({ pair }) => { pair.a },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5)).unwrap(), 5);
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 3);
	}

	/// Nested struct patterns project through both levels and bind a field
	/// from the inner struct.
	#[test]
	fn a_nested_struct_match_projects_through_both_levels() {
		let source = r#"
            struct Point(x: i32, y: i32);
            struct Segment(a: Point, b: Point);
            func run(a: i32, b: i32, c: i32, d: i32) -> i32 {
                local s = Segment(Point(a, b), Point(c, d))
                match s {
                    Segment(Point(0, y), Point(_, z)) => { y + z },
                    Segment(Point(x, _), _) => { x },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32, i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (0, 5, 6, 7)).unwrap(), 12);
		assert_eq!(run.call(&mut store, (3, 4, 5, 6)).unwrap(), 3);
	}

	/// Binding a whole aggregate keeps all of its flat slots, so field reads
	/// still find their values.
	#[test]
	fn a_pattern_can_bind_a_whole_aggregate() {
		let source = r#"
            struct Pair(a: i32, b: i32);
            func run(a: i32, b: i32) -> i32 {
                local pair = Pair(a, b)
                match pair {
                    whole => { whole.a + whole.b },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 7);
	}

	/// `i16` patterns also sign-extend into the canonical scalar.
	#[test]
	fn a_narrow_signed_switch_uses_the_selector_width() {
		let source = r#"
            func run(x: i16) -> i32 {
                match x {
                    -2 => { 1 },
                    -1 => { 2 },
                    0 => { 3 },
                    _ => { 4 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, -2).unwrap(), 1);
		assert_eq!(run.call(&mut store, -1).unwrap(), 2);
		assert_eq!(run.call(&mut store, 0).unwrap(), 3);
		assert_eq!(run.call(&mut store, 5).unwrap(), 4);
	}

	/// Unsigned narrow pattern bits are not sign-extended.
	#[test]
	fn an_unsigned_narrow_pattern_keeps_its_value() {
		let source = r#"
            func run(x: u8) -> i32 {
                match x {
                    255 => { 1 },
                    0 => { 2 },
                    1 => { 3 },
                    _ => { 4 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 255).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
		assert_eq!(run.call(&mut store, 1).unwrap(), 3);
		assert_eq!(run.call(&mut store, 7).unwrap(), 4);
	}

	/// An `i64` selector uses the compare chain but keeps all 64 bits.
	#[test]
	fn a_64_bit_selector_keeps_its_width() {
		let source = r#"
            func run(x: i64) -> i32 {
                match x {
                    -1 => { 1 },
                    0 => { 2 },
                    _ => { 3 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i64, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, -1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
		assert_eq!(run.call(&mut store, 1 << 40).unwrap(), 3);
	}

	/// A float constant pattern has no total equality, so it is rejected by
	/// checking before lowering.
	#[test]
	fn a_float_constant_pattern_is_rejected_by_the_eq_bound() {
		let source = r#"
            const ZERO: f64 = 0.0;
            func run(x: f64) -> i32 {
                match x {
                    const ZERO => { 1 },
                    _ => { 2 },
                }
            }
            export { run as "run" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let diagnostics = match crate::tir::build(&mut graph) {
			Ok(_) => panic!("a float constant pattern has no equality"),
			Err(diagnostics) => diagnostics,
		};
		assert!(
			diagnostics.iter().any(|d| {
				d.message.contains("`f64: Eq` is not satisfied")
					&& d.code.as_deref()
						== Some(DiagnosticCode::TraitBoundViolation.code())
			}),
			"expected an Eq trait-bound diagnostic, got {diagnostics:#?}"
		);
	}

	/// A float can still be bound; only equality tests are rejected.
	#[test]
	fn a_float_can_be_bound_in_a_match() {
		let source = r#"
            func run(x: f64) -> f64 {
                match x {
                    whole => { whole + 1.0 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<f64, f64>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 1.5).unwrap(), 2.5);
	}

	/// A structural match can be exhaustive without an irrefutable arm; the
	/// final `Unreachable` base is never actually reached.
	#[test]
	fn a_tree_match_can_be_exhaustive_without_a_wildcard() {
		let source = r#"
            struct Wrapper(value: Bool);
            func run(value: Bool) -> i32 {
                local w = Wrapper(value)
                match w {
                    Wrapper(const True) => { 1 },
                    Wrapper(const False) => { 2 },
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
	}

	/// A `break` inside an arm leaves the enclosing loop, not the match.
	#[test]
	fn a_break_in_a_match_arm_leaves_the_loop() {
		let source = r#"
            func run(n: i32) -> i32 {
                local mut i: i32 = 0
                loop {
                    match i {
                        3 => { break 7 },
                        _ => { i = i + 1 },
                    }
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 0).unwrap(), 7);
	}

	// ── short-circuiting ─────────────────────────────────────────────────

	/// A false left operand decides `&&`, so a right one that would trap is
	/// never evaluated.
	#[test]
	fn and_skips_a_right_operand_it_does_not_need() {
		let source = r#"
            use std::trap as stop;
            func run(a: i32) -> Bool { (a != a) && stop() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 7).unwrap(), 0);
	}

	/// A true left operand leaves `&&` to the right one, trap included.
	#[test]
	fn and_evaluates_a_right_operand_it_needs() {
		let source = r#"
            use std::trap as stop;
            func run(a: i32) -> Bool { (a == a) && stop() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, 7).is_err());
	}

	/// A true left operand decides `||`, so a right one that would trap is
	/// never evaluated.
	#[test]
	fn or_skips_a_right_operand_it_does_not_need() {
		let source = r#"
            use std::trap as stop;
            func run(a: i32) -> Bool { (a == a) || stop() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 7).unwrap(), 1);
	}

	/// A false left operand leaves `||` to the right one, trap included.
	#[test]
	fn or_evaluates_a_right_operand_it_needs() {
		let source = r#"
            use std::trap as stop;
            func run(a: i32) -> Bool { (a != a) || stop() }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, 7).is_err());
	}

	/// Chains short-circuit left to right: one deciding operand stops the
	/// rest of the chain.
	#[test]
	fn logical_chains_stop_at_the_deciding_operand() {
		let source = r#"
            use std::trap as stop;
            func and_chain(a: i32, b: i32) -> Bool {
                (a != a) && (b == b) && stop()
            }
            func or_chain(a: i32, b: i32) -> Bool {
                (a == a) || (b != b) || stop()
            }
            export { and_chain as "and_chain", or_chain as "or_chain" }
        "#;
		let (mut store, instance) = instantiate(source);
		let and_chain = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "and_chain")
			.expect("`and_chain` must be exported");
		assert_eq!(and_chain.call(&mut store, (0, 0)).unwrap(), 0);
		let or_chain = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "or_chain")
			.expect("`or_chain` must be exported");
		assert_eq!(or_chain.call(&mut store, (0, 0)).unwrap(), 1);
	}

	/// Constants short-circuit too, so `False && trap()` does not trap.
	#[test]
	fn constant_operands_short_circuit() {
		let source = r#"
            use std::trap as stop;
            func and_false() -> Bool { False && stop() }
            func and_true() -> Bool { True && True }
            func or_true() -> Bool { True || stop() }
            func or_false() -> Bool { False || False }
            export {
                and_false as "and_false", and_true as "and_true",
                or_true as "or_true", or_false as "or_false",
            }
        "#;
		let (mut store, instance) = instantiate(source);
		for (name, expected) in [
			("and_false", 0),
			("and_true", 1),
			("or_true", 1),
			("or_false", 0),
		] {
			let run = instance
				.get_typed_func::<(), i32>(&mut store, name)
				.unwrap_or_else(|_| panic!("`{name}` must be exported"));
			assert_eq!(run.call(&mut store, ()).unwrap(), expected, "{name}");
		}
	}

	/// A diverging left operand prevents either logical operator from
	/// evaluating its right one.
	#[test]
	fn a_diverging_left_operand_stops_both_operators() {
		let source = r#"
            use std::trap as stop;
            func and(a: i32) -> Bool { stop() && (a == a) }
            func or(a: i32) -> Bool { stop() || (a == a) }
            export { and as "and", or as "or" }
        "#;
		let (mut store, instance) = instantiate(source);
		for name in ["and", "or"] {
			let run = instance
				.get_typed_func::<i32, i32>(&mut store, name)
				.unwrap_or_else(|_| panic!("`{name}` must be exported"));
			assert!(run.call(&mut store, 7).is_err(), "{name}");
		}
	}

	/// A short-circuit result is an ordinary `Bool` condition.
	#[test]
	fn a_short_circuit_drives_an_if() {
		let source = r#"
            func run(a: i32, b: i32) -> i32 {
                if a == a && b != b { 1 } else { 2 }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 2);
	}

	// ── if / else ─────────────────────────────────────────────────────────

	/// Both branches are reachable and the chosen one supplies the value.
	#[test]
	fn an_if_chooses_its_branch_value() {
		let source = r#"
            func run(c: Bool) -> i32 { if c { 1 } else { 2 } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
	}

	/// An `if` without an `else` is a `()` expression whose branch may
	/// still update locals.
	#[test]
	fn an_if_without_else_is_a_unit_statement() {
		let source = r#"
            func run(c: Bool) -> i32 {
                local mut x: i32 = 0;
                if c { x = 1; }
                x
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 0);
	}

	/// An if result is an ordinary value: it initializes a local like any
	/// other expression.
	#[test]
	fn an_if_result_initializes_a_local() {
		let source = r#"
            func run(c: Bool) -> i32 {
                local x: i32 = if c { 3 } else { 4 };
                x + 1
            }
			export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 4);
		assert_eq!(run.call(&mut store, 0).unwrap(), 5);
	}

	/// A chain of `else if` nests `if`s in the else position; MIR requires
	/// every branch to be a block, so the nested `if` is wrapped.
	#[test]
	fn an_else_if_chain_selects_the_first_matching_branch() {
		let source = r#"
            func grade(n: i32) -> i32 {
                if n < 0 { 0 }
                else if n < 10 { 1 }
                else if n < 100 { 2 }
                else { 3 }
            }
            export { grade as "grade" }
        "#;
		let (mut store, instance) = instantiate(source);
		let grade = instance
			.get_typed_func::<i32, i32>(&mut store, "grade")
			.expect("`grade` must be exported");
		for (n, expected) in [(-1, 0), (5, 1), (50, 2), (500, 3)] {
			assert_eq!(grade.call(&mut store, n).unwrap(), expected, "n = {n}");
		}
	}

	/// A branch may leave the function; the `if` itself is then only a
	/// unit statement and the code after it still runs on the other path.
	#[test]
	fn a_return_in_a_branch_leaves_the_rest_of_the_body() {
		let source = r#"
            func run(c: Bool) -> i32 {
                if c { return 1; }
                2
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
	}

	/// A diverging branch contributes nothing: the other branch supplies
	/// the result, and taking the diverging one traps.
	#[test]
	fn a_diverging_branch_contributes_no_value() {
		let source = r#"
            use std::trap as stop;
            func then(c: Bool) -> i32 { if c { stop() } else { 2 } }
            func otherwise(c: Bool) -> i32 { if c { 1 } else { stop() } }
            export { then as "then", otherwise as "otherwise" }
        "#;
		let (mut store, instance) = instantiate(source);
		let then = instance
			.get_typed_func::<i32, i32>(&mut store, "then")
			.expect("`then` must be exported");
		assert!(then.call(&mut store, 1).is_err());
		assert_eq!(then.call(&mut store, 0).unwrap(), 2);
		let otherwise = instance
			.get_typed_func::<i32, i32>(&mut store, "otherwise")
			.expect("`otherwise` must be exported");
		assert_eq!(otherwise.call(&mut store, 1).unwrap(), 1);
		assert!(otherwise.call(&mut store, 0).is_err());
	}

	/// A diverging condition never enters either branch.
	#[test]
	fn a_diverging_if_condition_never_enters_a_branch() {
		let source = r#"
            use std::trap as stop;
            func run(c: Bool) -> i32 { if stop() { 1 } else { 2 } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, 1).is_err());
		assert!(run.call(&mut store, 0).is_err());
	}

	/// An `if` without `else` whose branch diverges still has unit type on
	/// the fallthrough path.
	#[test]
	fn an_if_without_else_may_take_a_diverging_branch() {
		let source = r#"
            use std::trap as stop;
            func run(c: Bool) { if c { stop() } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, ()>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, 1).is_err());
		run.call(&mut store, 0).unwrap();
	}

	/// A break inside an `if` branch targets the enclosing loop.
	#[test]
	fn a_break_in_an_if_branch_leaves_the_loop() {
		let source = r#"
            func run(c: Bool) -> i32 {
                loop {
                    if c { break 1; } else { break 2; }
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 1);
		assert_eq!(run.call(&mut store, 0).unwrap(), 2);
	}

	/// Multi-scalar branch values cross the if join like scalars do.
	#[test]
	fn an_aggregate_if_value_crosses_the_join() {
		let source = r#"
            func run(c: Bool) -> (i32, i32) {
                if c { (1, 2) } else { (3, 4) }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, (i32, i32)>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), (1, 2));
		assert_eq!(run.call(&mut store, 0).unwrap(), (3, 4));
	}

	/// Empty branches are unit-valued and have nothing to merge.
	#[test]
	fn empty_if_branches_are_unit() {
		let source = r#"
            func run(c: Bool) { if c {} else {} }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		instance
			.get_typed_func::<i32, ()>(&mut store, "run")
			.expect("`run` must be exported")
			.call(&mut store, 1)
			.unwrap();
	}

	/// Both branches diverging makes the whole `if` diverge.
	#[test]
	fn an_if_whose_branches_both_diverge_is_never() {
		let source = r#"
            use std::trap as stop;
            func run(c: Bool) -> ! {
                if c { stop() } else { stop() }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, ()>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, 1).is_err());
		assert!(run.call(&mut store, 0).is_err());
	}

	/// A diverging branch of an aggregate-valued `if` contributes no slots;
	/// the other branch still supplies the whole aggregate.
	#[test]
	fn a_diverging_branch_leaves_an_aggregate_value_intact() {
		let source = r#"
            use std::trap as stop;
            func run(c: Bool) -> (i32, i32) {
                if c { (1, 2) } else { stop() }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, (i32, i32)>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), (1, 2));
		assert!(run.call(&mut store, 0).is_err());
	}

	/// `continue` in an `if` branch restarts the enclosing loop; the other
	/// branch reaches the loop's break. Only the terminating input is run.
	#[test]
	fn a_continue_in_an_if_branch_restarts_the_loop() {
		let source = r#"
            func run(c: Bool) -> i32 {
                loop {
                    if c { continue; }
                    break 1;
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 0).unwrap(), 1);
	}

	/// A break inside an `if` branch can leave an enclosing labelled block,
	/// with the block's fallthrough as the other exit.
	#[test]
	fn a_break_in_an_if_branch_leaves_a_labelled_block() {
		let source = r#"
            func run(c: Bool) -> i32 {
                block :done {
                    if c { break :done 3; }
                    4
                }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i32, i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, 1).unwrap(), 3);
		assert_eq!(run.call(&mut store, 0).unwrap(), 4);
	}

	/// A nested `else if` may itself diverge on one branch.
	#[test]
	fn a_diverging_else_if_branch_still_joins_the_chain() {
		let source = r#"
            use std::trap as stop;
            func run(a: Bool, b: Bool) -> i32 {
                if a { 1 } else if b { stop() } else { 2 }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, (1, 0)).unwrap(), 1);
		assert!(run.call(&mut store, (0, 1)).is_err());
		assert_eq!(run.call(&mut store, (0, 0)).unwrap(), 2);
	}

	/// Aggregates travel through a wrapped `else if` branch like through a
	/// plain block branch.
	#[test]
	fn an_else_if_chain_joins_aggregate_values() {
		let source = r#"
            func run(a: Bool, b: Bool) -> (i32, i32) {
                if a { (1, 2) } else if b { (3, 4) } else { (5, 6) }
            }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i32), (i32, i32)>(&mut store, "run")
			.expect("`run` must be exported");
		assert_eq!(run.call(&mut store, (1, 0)).unwrap(), (1, 2));
		assert_eq!(run.call(&mut store, (0, 1)).unwrap(), (3, 4));
		assert_eq!(run.call(&mut store, (0, 0)).unwrap(), (5, 6));
	}

	/// A loop whose only exit is `continue` never returns; the module must
	/// still be valid Wasm. Instantiating does not run it.
	#[test]
	fn an_endless_loop_with_continue_encodes() {
		let source = r#"
            func run() -> ! { loop { continue; } }
            export { run as "run" }
        "#;
		let _ = instantiate(source);
	}

	/// A break whose value diverges never leaves the loop: the value traps
	/// first.
	#[test]
	fn a_diverging_break_value_never_breaks() {
		let source = r#"
            use std::trap as stop;
            func run() -> i32 { loop { break stop(); } }
            export { run as "run" }
        "#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.expect("`run` must be exported");
		assert!(run.call(&mut store, ()).is_err());
	}

	/// `continue` restarts the loop its label names, not the innermost loop.
	/// It always diverges, so this loop has no reachable break: the test
	/// builds the module and checks the resolved target rather than running
	/// it.
	#[test]
	fn continue_targets_the_loop_its_label_names() {
		let source = r#"
            func run() -> ! {
                loop :outer {
                    loop {
                        continue :outer;
                    }
                }
            }
            export { run as "run" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).expect("`continue` must lower");
		let function = &mir.functions[0];

		let mir::ExprKind::Block { expressions, .. } = &function.block.kind
		else {
			panic!("the body must be a block")
		};
		let mir::ExprKind::Loop {
			scope_index: outer,
			block: outer_body,
		} = &expressions[0].kind
		else {
			panic!("the body must contain the outer loop")
		};
		let mir::ExprKind::Block {
			expressions: outer_expressions,
			..
		} = &outer_body.kind
		else {
			panic!("a loop must contain a block")
		};
		let mir::ExprKind::Loop {
			scope_index: inner,
			block: inner_body,
		} = &outer_expressions[0].kind
		else {
			panic!("the outer loop must contain the inner loop")
		};
		let mir::ExprKind::Block {
			expressions: inner_expressions,
			..
		} = &inner_body.kind
		else {
			panic!("a loop must contain a block")
		};
		let mir::ExprKind::Continue { scope_index } =
			&inner_expressions[0].kind
		else {
			panic!("the inner loop must contain the continue")
		};

		assert_ne!(outer, inner, "each loop needs its own scope");
		assert_eq!(
			scope_index, outer,
			"`continue :outer` must restart the outer loop"
		);
	}
}
