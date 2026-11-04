//! TIR → MIR lowering for the first executable checkpoint.
//!
//! This is deliberately not a view or a second IR: it takes the live
//! [`TypeContext`] the checker already built, reads the checked tables
//! directly, and constructs [`mir::MIR`]. Type normalization and aggregate
//! layout need `&mut TypeContext`, which is why the entry point is mutable.
//!
//! The current checkpoints cover exported functions, direct calls, method
//! calls (a trait's declaration through the impl its `Self` selects, or the
//! default the impl inherits, and a function item's `Call::call` as a call
//! of the item), locals, blocks, returns, scalar operators (including
//! short-circuiting `&&`/`||`) and intrinsics (`transmute` as a MIR
//! `Transmute`, which only retypes), loops, breaks and continues
//! (including labelled blocks and loops), `if`/`else`, `match` (including
//! destructuring, `|` alternatives and char patterns), destructuring `local`
//! declarations, compound assignments, constants (`True`/`False`, enum
//! variants, free `const` items, and associated ones per instance), `Char`
//! literals, type aliases, and tuples and structs (including generic and
//! zero-sized fields).
//! Aggregates keep their values in declaration order while TIR supplies the
//! byte offsets and size. A constant pattern compares an aggregate through
//! the concrete `PartialEq::eq` impl its checked `Eq` bound selects, so a
//! type's own equality is honoured. Memory types (arrays, slices, pointers),
//! calls the compiler implements, function references, and float equality tests (floats have no total equality) are
//! not lowered yet. Every other checked form is reported as
//! `UnsupportedExpression`; no unsupported form becomes `Noop` and no
//! unsupported form disappears from the output.

use std::collections::{HashMap, VecDeque};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use string_interner::symbol::{Symbol, SymbolU32};

use super::body::{
	Body, ElementOrder, ExprIdx, ExprKind, FunctionImplementation, PatIdx,
	ScopeIdx,
};
use super::defs::{Attributes, FieldIdx, FunctionIdx, GlobalIdx};
use super::eval::Val;
use super::members::ResolvedFunction;
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

/// How a call's written arguments meet what it runs.
#[derive(Clone, Copy)]
enum Dispatch {
	/// The receiver, if any, is the first parameter and `args` the rest.
	Direct,
	/// `Call::call` of a function item: the receiver is the item, which is
	/// no parameter, and `args` fills the item's function.
	Item,
}

/// A function with the type arguments its body is lowered with, flat as
/// TIR's call nodes hold them (an impl's, then its own; `[Self, own...]` for
/// a trait's default). `args` is the list of the interned item type
/// (`Type::Function`), so equal instances are equal; empty for a function with
/// no parameters, which is its own one instance. The counterpart of
/// `eval::Instance`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FunctionInstance {
	function: FunctionIdx,
	args: TypeList,
}

impl FunctionInstance {
	fn of(function: FunctionIdx) -> Self {
		Self {
			function,
			args: TypeList::EMPTY,
		}
	}
}

/// What one function's lowering keeps outside the shared [`Lowerer`].
struct FunctionState {
	file_id: FileId,
	/// The function's type environment, which its body's types are written
	/// in, and the instance's arguments for its parameters. A body type is
	/// made concrete with both where it is read (`Lowerer::expr_ty`); every
	/// type past that point has no parameter.
	env: TypeEnvIdx,
	args: Box<[TypeIndex]>,
	/// The instance being lowered, which a call in its body records as the
	/// callee's caller.
	instance: FunctionInstance,
	/// `body.locals()[i]` in the MIR local it was assigned.
	local_map: Vec<mir::LocalIndex>,
	/// MIR locals: the declared parameters first (including discard slots for
	/// unnamed ones), then every remaining source local.
	locals: Vec<mir::Local>,
	/// The function's MIR nodes.
	mir_body: mir::Body,
	/// The label of each of the body's scopes (indexed by `ScopeIdx`) that a
	/// `break` or `continue` names, or a loop owns, given on first use. A
	/// block whose scope has none is a `Sequence`.
	labels: Vec<Option<mir::LabelId>>,
	label_count: u32,
	/// The body's root, once it is lowered.
	root: Option<mir::ExprId>,
}

impl FunctionState {
	fn push(&mut self, kind: mir::ExprKind, ty: mir::ValueType) -> mir::ExprId {
		self.mir_body.push(kind, ty)
	}

	fn ty(&self, expr: mir::ExprId) -> mir::ValueType {
		self.mir_body.ty(expr)
	}

	fn list(
		&mut self,
		items: impl IntoIterator<Item = mir::ExprId>,
	) -> mir::ExprList {
		self.mir_body.push_list(items)
	}

	/// A boolean literal: Wasm has none, so MIR holds it as an integer
	/// `0`/`1` of type `Bool`.
	fn boolean(&mut self, value: bool) -> mir::ExprId {
		self.push(
			mir::ExprKind::Int {
				value: i64::from(value),
			},
			mir::ValueType::Bool,
		)
	}

	/// `scope`'s label, given on first use.
	fn label(&mut self, scope: ScopeIdx) -> mir::LabelId {
		let slot = &mut self.labels[usize::from(scope)];
		*slot.get_or_insert_with(|| {
			let label = mir::LabelId::new(self.label_count);
			self.label_count += 1;
			label
		})
	}

	/// `statements` as a block of `scope`: a `Block` with its label when
	/// something inside jumps out of it, a `Sequence` otherwise.
	fn block(
		&mut self,
		scope: ScopeIdx,
		statements: Vec<mir::ExprId>,
		ty: mir::ValueType,
	) -> mir::ExprId {
		let statements = self.list(statements);
		match self.labels[usize::from(scope)] {
			Some(label) => {
				self.push(mir::ExprKind::Block { label, statements }, ty)
			}
			None => self.push(mir::ExprKind::Sequence { statements }, ty),
		}
	}
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
	/// Index-aligned with `functions`.
	function_flags: Vec<mir::FunctionFlags>,
	/// One entry per imported item lowered, in the order lowering met them.
	imports: Vec<mir::Import>,
	/// Indexed by `GlobalId`.
	globals: Vec<mir::Global>,
	/// Each source global's backend identity, given the first time something
	/// names it; indexed by `GlobalIdx`.
	global_ids: Vec<Option<mir::GlobalId>>,
	signatures: Vec<mir::FunctionSignature>,
	/// Backend identity, minted here per instance. Never a source or Wasm
	/// index.
	ids: HashMap<FunctionInstance, mir::FunctionId>,
	/// Concrete source types already translated into flat representations.
	aggregate_types: HashMap<TypeIndex, AggregateLowering>,
	aggregates: AggregateTable,
	pending: VecDeque<FunctionInstance>,
	/// The instance whose body first named each instance; the roots (the
	/// exports) have none. Read by the recursion limit.
	callers: HashMap<FunctionInstance, FunctionInstance>,
	next_id: u32,
}

/// How many instances of one function may nest along a chain of callers,
/// rustc's default `recursion_limit`.
const RECURSION_LIMIT: u32 = 128;

/// How many Wasm values one type may flatten to. A resource limit, not a
/// language rule: interned types share their parts, so a doubling chain
/// (`f((x, x))` in `f<T>`) is a handful of types that flatten to
/// exponentially many values, long before the recursion limit stops it.
/// Far above what a program writes by hand.
const SLOT_LIMIT: usize = 1 << 16;

/// The separate build entry point. `check` is untouched; this repeats its
/// setup and then lowers the same live context instead of dropping it.
pub(super) fn build(
	context: &mut TypeContext<'_, '_, '_>,
) -> Result<mir::MIR, ()> {
	let global_count = context.defs.globals.len();
	Lowerer {
		context,
		functions: Vec::new(),
		function_flags: Vec::new(),
		imports: Vec::new(),
		globals: Vec::new(),
		global_ids: vec![None; global_count],
		signatures: Vec::new(),
		ids: HashMap::new(),
		aggregate_types: HashMap::new(),
		aggregates: AggregateTable::default(),
		pending: VecDeque::new(),
		callers: HashMap::new(),
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
					let id = self.enqueue(FunctionInstance::of(function));
					mir_exports.push(mir::Export {
						name,
						item: mir::Item::Function(id),
					});
				}
				super::signatures::ExportedItem::Global(global) => {
					let id = self.global(global)?;
					mir_exports.push(mir::Export {
						name,
						item: mir::Item::Global(id),
					});
				}
				super::signatures::ExportedItem::Memory(_) => {
					let source = self
						.context
						.defs
						.exports
						.get(&name)
						.expect("every checked export has a source entry");
					self.unsupported(
						source.external_span.file_id,
						source.external_span.span,
						"exporting a memory",
					)?;
				}
			}
		}

		while let Some(instance) = self.pending.pop_front() {
			self.lower_function(instance)?;
		}

		let mir = mir::MIR {
			functions: self.functions,
			function_flags: self.function_flags,
			signatures: self.signatures,
			globals: self.globals,
			exports: mir_exports,
			imports: self.imports,
			memories: Vec::new(),
			aggregates: self.aggregates.finish(),
			static_entries: Vec::new(),
			start_function: None,
		};
		if cfg!(debug_assertions)
			&& let Err(import) = mir.verify_imports()
		{
			panic!("import entry {import:?} and its item disagree");
		}
		Ok(mir)
	}

	/// The instance of `function` with the concrete `args`.
	fn instance(
		&mut self,
		function: FunctionIdx,
		args: &[TypeIndex],
	) -> FunctionInstance {
		if args.is_empty() {
			return FunctionInstance::of(function);
		}
		debug_assert!(
			args.iter().all(|&arg| !self.context.types.has_param(arg)),
			"an instance's arguments are concrete"
		);
		let item = self.context.types.intern_function(function, args);
		let Type::Function { type_args, .. } =
			*self.context.types.resolve(item)
		else {
			unreachable!("a function interns as a `Type::Function`")
		};
		FunctionInstance {
			function,
			args: type_args,
		}
	}

	/// What a call in `state`'s body runs: `function` with the call's
	/// `type_args`, made concrete with the caller's own, and, for a trait's
	/// declaration, the member the impl its `Self` selects provides.
	fn resolve_call(
		&mut self,
		state: &FunctionState,
		function: FunctionIdx,
		type_args: TypeList,
		span: TextSpan,
	) -> Result<(FunctionInstance, Dispatch), ()> {
		let written: Vec<TypeIndex> =
			self.context.types.list(type_args).to_vec();
		let args: Vec<TypeIndex> = written
			.into_iter()
			.map(|arg| self.substitute(arg, state.env, &state.args))
			.collect();
		let (function, args, dispatch) =
			match self.context.resolve_function(function, &args) {
				Ok(ResolvedFunction::Instance { function, args }) => {
					(function, args, Dispatch::Direct)
				}
				Ok(ResolvedFunction::Item { function, args }) => {
					(function, args, Dispatch::Item)
				}
				Ok(ResolvedFunction::Builtin) => {
					self.unsupported(
						state.file_id,
						span,
						"a call the compiler implements (a function \
						 reference's or a slice's)",
					)?;
					unreachable!()
				}
				Ok(ResolvedFunction::Abstract) => {
					unreachable!("an instance's arguments are concrete")
				}
				// The checker proved the bound, so only a reported failure
				// reaches here.
				Err(_) => return Err(()),
			};
		Ok((self.instance(function, &args), dispatch))
	}

	/// The instance a call in `state`'s body runs, queued, for an operator
	/// trait's method, which is never a function item's `Call::call`.
	fn callee(
		&mut self,
		state: &FunctionState,
		function: FunctionIdx,
		type_args: TypeList,
		span: TextSpan,
	) -> Result<(FunctionInstance, mir::FunctionId), ()> {
		let (instance, dispatch) =
			self.resolve_call(state, function, type_args, span)?;
		debug_assert!(matches!(dispatch, Dispatch::Direct));
		let id = self.enqueue_from(state, instance, span)?;
		Ok((instance, id))
	}

	/// `instance`'s backend identity, named at `span` in `state`'s body.
	///
	/// A new instance remembers its caller, which bounds polymorphic
	/// recursion as rustc's recursion limit does: an instance nested inside
	/// more than [`RECURSION_LIMIT`] instances of its own function, along the
	/// chain of callers that first named each, is an error. Only a generic
	/// function can get there, since a recursive call with the same
	/// arguments is the same instance.
	fn enqueue_from(
		&mut self,
		state: &FunctionState,
		instance: FunctionInstance,
		span: TextSpan,
	) -> Result<mir::FunctionId, ()> {
		if let Some(&id) = self.ids.get(&instance) {
			return Ok(id);
		}
		let mut depth = 1;
		let mut at = Some(state.instance);
		while let Some(caller) = at {
			if caller.function == instance.function {
				depth += 1;
			}
			at = self.callers.get(&caller).copied();
		}
		if depth > RECURSION_LIMIT {
			let function =
				&self.context.defs.functions[usize::from(instance.function)];
			let (definition_file, definition_span) =
				(function.file_id, function.name.span);
			let item = self.context.types.intern_function(
				instance.function,
				self.context.types.list(instance.args).to_vec().as_slice(),
			);
			let name = self.context.type_formatter().display_type(item);
			self.context.diagnostics.push(
				Diagnostic::error()
					.with_code(DiagnosticCode::RecursionLimit.code())
					.with_message(format!(
						"reached the recursion limit while instantiating `{name}`"
					))
					.with_label(
						Label::primary(state.file_id, span)
							.with_message("this call instantiates it"),
					)
					.with_label(
						Label::secondary(definition_file, definition_span)
							.with_message("the function is defined here"),
					)
					.with_note(format!(
						"each instance is called with new type arguments, so \
						 instantiating it never ends; the limit is \
						 {RECURSION_LIMIT} nested instances of one function"
					)),
			);
			return Err(());
		}
		self.callers.insert(instance, state.instance);
		Ok(self.enqueue(instance))
	}

	/// `instance`'s backend identity, queueing its body the first time.
	fn enqueue(&mut self, instance: FunctionInstance) -> mir::FunctionId {
		if let Some(&id) = self.ids.get(&instance) {
			return id;
		}
		let id = mir::FunctionId::new(self.next_id);
		self.next_id += 1;
		self.ids.insert(instance, id);
		self.pending.push_back(instance);
		id
	}

	fn lower_function(&mut self, instance: FunctionInstance) -> Result<(), ()> {
		let function = instance.function;
		let id = self.ids[&instance];
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
			&FunctionImplementation::Imported(import) => {
				return self.lower_imported_function(instance, import);
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
		let (signature_index, param_types, result_type) =
			self.lower_signature(instance)?;
		let env = self.context.functions[usize::from(function)].type_params;
		let args: Box<[TypeIndex]> =
			self.context.types.list(instance.args).into();

		let implementation = std::mem::replace(
			&mut self.context.function_implementations[usize::from(function)],
			FunctionImplementation::Declaration,
		);
		let lowered = self.lower_body(
			instance,
			file_id,
			env,
			args,
			implementation
				.body()
				.expect("only a defined function enters body lowering"),
			&param_types,
			result_type,
		);
		// Put the checked body back: lowering borrows it, it does not consume it.
		self.context.function_implementations[usize::from(function)] =
			implementation;
		let state = lowered?;
		let root = state.root.expect("a lowered body has a root");
		if cfg!(debug_assertions)
			&& let Err(error) = mir::body::verify(
				&state.mir_body,
				root,
				&state.locals,
				state.label_count,
			) {
			panic!("lowering broke the MIR arena's invariants: {error:?}");
		}
		// Instances are lowered in the order their ids were given, so a
		// function's id is its index.
		debug_assert_eq!(usize::from(id), self.functions.len());
		self.functions.push(mir::Function {
			signature_index,
			origin: mir::Origin::Defined(mir::Code {
				locals: state.locals,
				label_count: state.label_count,
				body: state.mir_body,
				root,
			}),
		});
		// Every instance of an `#[inline]` function is inline: the attribute
		// is on the declaration, and an instance only fills its parameters.
		let mut flags = mir::FunctionFlags::empty();
		if self.context.defs.functions[usize::from(function)]
			.attributes
			.contains(Attributes::INLINE)
		{
			flags.insert(mir::FunctionFlags::INLINE);
		}
		self.function_flags.push(flags);
		Ok(())
	}

	/// An imported function: its signature, and the import entry naming it.
	/// The host provides it as `module`.`name`, with `name` its written name.
	fn lower_imported_function(
		&mut self,
		instance: FunctionInstance,
		import: super::defs::ImportIdx,
	) -> Result<(), ()> {
		let id = self.ids[&instance];
		let (signature_index, _, _) = self.lower_signature(instance)?;
		let entry =
			mir::ImportIdx::new(u32::try_from(self.imports.len()).unwrap());
		self.imports.push(mir::Import {
			module: self.context.defs.imports[usize::from(import)]
				.external_name
				.inner,
			name: self.context.defs.functions[usize::from(instance.function)]
				.name
				.inner,
			item: mir::Item::Function(id),
		});
		debug_assert_eq!(usize::from(id), self.functions.len());
		self.functions.push(mir::Function {
			signature_index,
			origin: mir::Origin::Imported(entry),
		});
		self.function_flags.push(mir::FunctionFlags::empty());
		Ok(())
	}

	/// `global`'s backend identity, lowering it the first time: its one Wasm
	/// value's type, and an import entry or its compile-time value.
	pub(super) fn global(
		&mut self,
		global: GlobalIdx,
	) -> Result<mir::GlobalId, ()> {
		if let Some(id) = self.global_ids[usize::from(global)] {
			return Ok(id);
		}
		let def = &self.context.defs.globals[usize::from(global)];
		let (file_id, name, mutable) =
			(def.file_id, def.name, def.mut_trait_impl_index.is_some());
		let value_type = self.context.global_value_type(global);
		let ty = self.lower_type(value_type, file_id, name.span)?;
		// The checker proved it one Wasm value: a scalar, or a pack of one
		// (`Meters(u32)`), which the module holds as that scalar.
		let ty = match ty {
			mir::ValueType::Aggregate { aggregate_index } => {
				let [scalar] = *self.aggregates.get(aggregate_index).scalars
				else {
					unreachable!("a global's value is one Wasm value")
				};
				scalar
			}
			ty => ty,
		};
		let id = mir::GlobalId::new(u32::try_from(self.globals.len()).unwrap());
		let origin =
			match self.context.ast_node(super::defs::DefId::Global(global)) {
				&super::defs::AstNodeRef::ImportedGlobal {
					import_index,
					..
				} => {
					let entry = mir::ImportIdx::new(
						u32::try_from(self.imports.len()).unwrap(),
					);
					self.imports.push(mir::Import {
						module: self.context.defs.imports
							[usize::from(import_index)]
						.external_name
						.inner,
						name: name.inner,
						item: mir::Item::Global(id),
					});
					mir::Origin::Imported(entry)
				}
				_ => {
					let value = self.context.global_values[usize::from(global)]
						.as_deref()
						.expect("a checked global without errors has a value");
					let [scalar] = value else {
						unreachable!("a global's value is one Wasm value")
					};
					mir::Origin::Defined(match scalar.val {
						Val::I32(bits) => {
							mir::ConstInit::Int(i64::from(bits as i32))
						}
						Val::I64(bits) => mir::ConstInit::Int(bits as i64),
						Val::F32(bits) => mir::ConstInit::Float(f64::from(
							f32::from_bits(bits),
						)),
						Val::F64(bits) => {
							mir::ConstInit::Float(f64::from_bits(bits))
						}
						Val::MemoryOffset { .. } | Val::V128(_) => {
							self.unsupported(
								file_id,
								name.span,
								"a global holding an address (the memory checkpoint)",
							)?;
							unreachable!()
						}
					})
				}
			};
		self.globals.push(mir::Global {
			id,
			ty,
			mutability: if mutable {
				mir::Mutability::Mutable
			} else {
				mir::Mutability::Immutable
			},
			origin,
		});
		self.global_ids[usize::from(global)] = Some(id);
		Ok(id)
	}

	/// `instance`'s MIR signature, and its parameter and result types.
	fn lower_signature(
		&mut self,
		instance: FunctionInstance,
	) -> Result<(mir::SignatureIndex, Vec<mir::ValueType>, mir::ValueType), ()>
	{
		let function = instance.function;
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
		// The flat arguments cover the whole parameter chain: an enclosing
		// impl's, then the function's own. Every instance comes from a
		// checked call, and the checker refuses to export a generic function
		// (E2019), so a missing argument is a broken invariant.
		assert_eq!(
			self.context.type_envs.identity_args(type_params).len(),
			instance.args.len(),
			"an instance has an argument for every parameter in its chain"
		);

		// Copy the lists out so lowering a type may borrow the context mutably.
		let args: Box<[TypeIndex]> =
			self.context.types.list(instance.args).into();
		let params: Vec<TypeIndex> =
			self.context.types.list(param_list).to_vec();
		let mut param_types = Vec::with_capacity(params.len());
		for ty in params {
			let ty = self.substitute(ty, type_params, &args);
			param_types.push(self.lower_type(ty, file_id, name_span)?);
		}
		let return_type = self.substitute(return_type, type_params, &args);
		let result_type = self.lower_type(return_type, file_id, name_span)?;

		let mut items = param_types.clone();
		items.push(result_type);
		let index =
			self.intern_signature(items.into_boxed_slice(), param_types.len());
		Ok((index, param_types, result_type))
	}

	/// `ty`, written where `env`'s parameters are in scope, with `args` for
	/// them. Not normalized: `lower_type` normalizes what it lowers.
	fn substitute(
		&mut self,
		ty: TypeIndex,
		env: TypeEnvIdx,
		args: &[TypeIndex],
	) -> TypeIndex {
		let ty = self.context.types.substitute(
			ty,
			Substitution {
				envs: &self.context.type_envs,
				env,
				args,
			},
		);
		debug_assert!(
			!self.context.types.has_param(ty),
			"an instance's types are concrete"
		);
		ty
	}

	/// The concrete type of `pattern` in this instance.
	fn pattern_ty(
		&mut self,
		body: &Body,
		state: &FunctionState,
		pattern: PatIdx,
	) -> TypeIndex {
		self.substitute(body.pattern_ty(pattern), state.env, &state.args)
	}

	/// The concrete type of `expr` in this instance.
	fn expr_ty(
		&mut self,
		body: &Body,
		state: &FunctionState,
		expr: ExprIdx,
	) -> TypeIndex {
		self.substitute(body.ty(expr), state.env, &state.args)
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
		instance: FunctionInstance,
		file_id: FileId,
		env: TypeEnvIdx,
		args: Box<[TypeIndex]>,
		body: &Body,
		param_types: &[mir::ValueType],
		result_type: mir::ValueType,
	) -> Result<FunctionState, ()> {
		if body.params().len() != param_types.len() {
			self.unsupported(
				file_id,
				self.context.defs.functions[usize::from(instance.function)]
					.name
					.span,
				"a parameter list that does not match its checked signature",
			)?;
		}

		let mut state = FunctionState {
			file_id,
			env,
			args,
			instance,
			local_map: vec![mir::LocalIndex::new(0); body.locals().len()],
			locals: Vec::new(),
			mir_body: mir::Body::default(),
			labels: vec![None; body.scope_count()],
			label_count: 0,
			root: None,
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
			let ty = self.substitute(local.ty, env, &state.args);
			let ty = self.lower_type(ty, file_id, local.name.span)?;
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

		let root = self.lower_expr(body, &mut state, body.root())?;
		let root_ty = state.ty(root);
		state.root = Some(root);
		if root_ty != result_type
			&& root_ty != mir::ValueType::Never
			&& root_ty != mir::ValueType::Unit
		{
			self.unsupported(
				file_id,
				body.span(body.root()),
				"a function body whose type differs from its declared result",
			)?;
		}

		Ok(state)
	}

	fn lower_expr(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
	) -> Result<mir::ExprId, ()> {
		let ty = self.expr_ty(body, state, expr);
		let ty = self.lower_type(ty, state.file_id, body.span(expr))?;
		let kind = body.kind(expr);
		match kind {
			ExprKind::Int(bits) => {
				let kind = match ty {
					mir::ValueType::F32 | mir::ValueType::F64 => {
						mir::ExprKind::Float { value: bits as f64 }
					}
					_ => mir::ExprKind::Int { value: bits as i64 },
				};
				Ok(state.push(kind, ty))
			}
			ExprKind::Float(value) => {
				Ok(state.push(mir::ExprKind::Float { value }, ty))
			}
			ExprKind::Local(local) => {
				let local = state.local_map[usize::from(local)];
				Ok(state.push(mir::ExprKind::LocalGet { local }, ty))
			}
			ExprKind::PrimitiveUnary { op, operand } => {
				if ty == mir::ValueType::Never {
					// The operand diverges, so the operator never runs. Do
					// not make a `Never`-typed instruction out of it; the
					// operand's own expression already carries the
					// divergence and the effects that preceded it.
					debug_assert_eq!(body.ty(operand), TypeIndex::NEVER);
					let operand = self.lower_expr(body, state, operand)?;
					debug_assert_eq!(state.ty(operand), mir::ValueType::Never);
					return Ok(operand);
				}
				let value = self.lower_expr(body, state, operand)?;
				let op = match op {
					UnaryOp::InvertSign => mir::UnaryOp::Neg,
					UnaryOp::Not => mir::UnaryOp::Eqz,
					UnaryOp::BitNot => mir::UnaryOp::BitNot,
				};
				Ok(state.push(mir::ExprKind::Unary { op, value }, ty))
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
					debug_assert_eq!(state.ty(left), mir::ValueType::Never);
					return Ok(left);
				}
				let lhs = self.lower_expr(body, state, lhs)?;
				let rhs = self.lower_expr(body, state, rhs)?;
				let Some(kind) = binary_kind(op, lhs, rhs) else {
					self.unsupported(
						state.file_id,
						body.span(expr),
						"an assignment operator in a value position",
					)?;
					unreachable!()
				};
				Ok(state.push(kind, ty))
			}
			ExprKind::Call {
				function,
				type_args,
				args,
			}
			| ExprKind::AbstractCall {
				method: function,
				type_args,
				args,
			} => self.lower_call(
				body, state, expr, function, type_args, None, args, ty,
			),
			ExprKind::MethodCall {
				function,
				type_args,
				receiver,
				args,
			}
			| ExprKind::AbstractMethodCall {
				method: function,
				type_args,
				receiver,
				args,
			} => self.lower_call(
				body,
				state,
				expr,
				function,
				type_args,
				Some(receiver),
				args,
				ty,
			),
			// A function item's value is zero-sized; a call of it names its
			// function by its type. A global's handle is too: `Global::get`
			// names the global by its type argument.
			ExprKind::Function { .. } | ExprKind::Global(_) => {
				Ok(state.push(mir::ExprKind::Noop, ty))
			}
			ExprKind::Tuple { elements, order } => {
				if ty == mir::ValueType::Unit {
					// `()` is the empty tuple; its only value is Unit.
					return Ok(state.push(mir::ExprKind::Noop, ty));
				}
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
				let mut lowered = Vec::new();
				for &statement in body.args(statements) {
					lowered.push(self.lower_expr(body, state, statement)?);
				}
				if let Some(result) = result {
					lowered.push(self.lower_expr(body, state, result)?);
				}
				// Lowered first, so a `break` inside has already given the
				// scope its label if it needs one.
				Ok(state.block(scope, lowered, ty))
			}
			ExprKind::Loop { scope, statements } => {
				// A loop always owns a label: `opt` builds it as a loop
				// block, which `break` leaves and `continue` restarts.
				let label = state.label(scope);
				let mut lowered = Vec::new();
				for &statement in body.args(statements) {
					lowered.push(self.lower_expr(body, state, statement)?);
				}
				// A body runs repeatedly and yields nothing; only a `break`
				// leaves the loop with a value.
				let statements = state.list(lowered);
				let loop_body = state.push(
					mir::ExprKind::Sequence { statements },
					mir::ValueType::Unit,
				);
				Ok(state.push(
					mir::ExprKind::Loop {
						label,
						body: loop_body,
					},
					ty,
				))
			}
			ExprKind::Break { scope, value } => {
				let value = match value {
					Some(value) => Some(self.lower_expr(body, state, value)?),
					None => None,
				};
				let label = state.label(scope);
				Ok(state.push(mir::ExprKind::Break { label, value }, ty))
			}
			ExprKind::Continue { scope } => {
				let label = state.label(scope);
				Ok(state.push(mir::ExprKind::Continue { label }, ty))
			}
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let condition = self.lower_expr(body, state, condition)?;
				let then = self.lower_expr(body, state, then_block)?;
				let otherwise = match else_block {
					Some(else_block) => {
						Some(self.lower_expr(body, state, else_block)?)
					}
					None => None,
				};
				Ok(state.push(
					mir::ExprKind::IfElse {
						condition,
						then,
						otherwise,
					},
					ty,
				))
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
						let value = state.push(
							mir::ExprKind::Int { value: codepoint },
							mir::ValueType::U32,
						);
						let values = state.list([value]);
						Ok(state.push(mir::ExprKind::Aggregate { values }, ty))
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
						Ok(state
							.push(mir::ExprKind::Int { value: codepoint }, ty))
					}
				}
			}
			ExprKind::Match { scrutinee, arms } => {
				self.lower_match(body, state, scrutinee, arms, ty)
			}
			ExprKind::Const {
				constant,
				type_args,
			}
			| ExprKind::AbstractConst {
				constant,
				type_args,
			} => self.lower_constant(body, state, expr, constant, type_args, ty),
			ExprKind::LocalDeclaration { pattern, value } => {
				self.lower_local_declaration(body, state, value, pattern, ty)
			}
			ExprKind::Assign { target, value } => {
				let value = self.lower_expr(body, state, value)?;
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
			}
			| ExprKind::AbstractCompoundAssign {
				method,
				type_args,
				target,
				value,
			} => self.lower_compound_assign_call(
				body,
				state,
				target,
				value,
				method,
				type_args,
				body.span(expr),
			),
			ExprKind::Drop { value } => {
				let value = self.lower_expr(body, state, value)?;
				Ok(state.push(mir::ExprKind::Drop { value }, ty))
			}
			ExprKind::Return { value } => {
				let value = match value {
					Some(value) => Some(self.lower_expr(body, state, value)?),
					None => None,
				};
				Ok(state.push(mir::ExprKind::Return { value }, ty))
			}

			// Checked forms the first checkpoint does not lower yet. Listed
			// exhaustively so a new TIR variant forces a decision here.
			ExprKind::Error
			| ExprKind::String(_)
			| ExprKind::Array { .. }
			| ExprKind::ArrayRepeat { .. }
			| ExprKind::NextDiscriminant(_)
			| ExprKind::CallRef { .. }
			| ExprKind::Load(_)
			| ExprKind::AddressOf(_)
			| ExprKind::Store { .. }
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

	/// The MIR node for a direct call to `callee`. `arguments` are already
	/// lowered in evaluation order.
	fn build_call(
		&mut self,
		state: &mut FunctionState,
		callee: mir::FunctionId,
		arguments: Vec<mir::ExprId>,
		ty: mir::ValueType,
	) -> mir::ExprId {
		let args = state.list(arguments);
		state.push(
			mir::ExprKind::Call {
				function: callee,
				args,
			},
			ty,
		)
	}

	/// A call of `function` with `type_args`, as `Call`/`AbstractCall` hold
	/// it, or, with a `receiver`, as `MethodCall`/`AbstractMethodCall` do.
	/// `args` is the value of the parameters after the receiver.
	#[allow(clippy::too_many_arguments)]
	fn lower_call(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		function: FunctionIdx,
		type_args: TypeList,
		receiver: Option<ExprIdx>,
		args: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let span = body.span(expr);
		let (callee, dispatch) =
			self.resolve_call(state, function, type_args, span)?;
		let mut prefix = Vec::new();
		let receiver = match (receiver, dispatch) {
			(Some(receiver), Dispatch::Direct) => {
				Some(self.lower_expr(body, state, receiver)?)
			}
			// A function item is zero-sized: it runs for its effects, before
			// the arguments, and is no parameter of the item's function.
			(Some(receiver), Dispatch::Item) => {
				let receiver = self.lower_expr(body, state, receiver)?;
				if state.ty(receiver) == mir::ValueType::Never {
					return Ok(receiver);
				}
				prefix.push(receiver);
				None
			}
			(None, _) => None,
		};
		if let FunctionImplementation::Intrinsic(intrinsic) =
			self.context.function_implementations[usize::from(callee.function)]
		{
			debug_assert!(receiver.is_none(), "an intrinsic is no method");
			let call = self.lower_intrinsic(
				body, state, expr, callee, intrinsic, args, ty,
			)?;
			return Ok(self.sequence(state, prefix, call));
		}
		let callee_id = self.enqueue_from(state, callee, span)?;
		let (_, callee_params, ..) = self.lower_signature(callee)?;
		// A lone remaining parameter is its value, so it must not be
		// unpacked even when that value is itself a tuple.
		let remaining = callee_params.len() - usize::from(receiver.is_some());
		let arguments = if remaining == 1 {
			vec![self.lower_expr(body, state, args)?]
		} else {
			self.lower_arguments(body, state, args, &mut prefix)?
		};
		let mut call_arguments = Vec::with_capacity(arguments.len() + 1);
		if let Some(receiver) = receiver {
			// Reordering or spilling the remaining arguments puts them in
			// `prefix`, which runs before the call's own arguments. Carry the
			// receiver through a temporary so it still runs first.
			let receiver = if prefix.is_empty() {
				receiver
			} else {
				let (set, get) = self.spill(state, receiver);
				prefix.insert(0, set);
				get
			};
			call_arguments.push(receiver);
		}
		call_arguments.extend(arguments);
		let call = self.build_call(state, callee_id, call_arguments, ty);
		Ok(self.sequence(state, prefix, call))
	}

	/// `value` stored in a fresh temporary: the store, and a read of it.
	fn spill(
		&mut self,
		state: &mut FunctionState,
		value: mir::ExprId,
	) -> (mir::ExprId, mir::ExprId) {
		let ty = state.ty(value);
		let local = self.push_temp_local(state, ty);
		let set = state.push(
			mir::ExprKind::LocalSet { local, value },
			mir::ValueType::Unit,
		);
		let get = state.push(mir::ExprKind::LocalGet { local }, ty);
		(set, get)
	}

	/// Lower a call's argument value into one MIR argument per parameter, in
	/// parameter order. The TIR value is a tuple with its written-order
	/// permutation, or the single value of a one-parameter call.
	fn lower_arguments(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		args: ExprIdx,
		prefix: &mut Vec<mir::ExprId>,
	) -> Result<Vec<mir::ExprId>, ()> {
		let ExprKind::Tuple { elements, order } = body.kind(args) else {
			let value = self.lower_expr(body, state, args)?;
			let source_ty = self.expr_ty(body, state, args);
			let source_ty =
				self.normalize_type(source_ty, state.file_id, body.span(args))?;
			if !matches!(
				self.context.types.resolve(source_ty),
				Type::Tuple { .. }
			) {
				return Ok(vec![value]);
			}
			// A computed argument tuple is evaluated once. Its source fields
			// may each be a subpack or Unit, not necessarily a single slot.
			let value_ty = state.ty(value);
			let local = self.push_temp_local(state, value_ty);
			prefix.push(state.push(
				mir::ExprKind::LocalSet { local, value },
				mir::ValueType::Unit,
			));
			let field_types = self.aggregate_field_types(
				source_ty,
				state.file_id,
				body.span(args),
			)?;
			let mut result = Vec::with_capacity(field_types.len());
			for (at, field_ty) in field_types.into_iter().enumerate() {
				let ty =
					self.lower_type(field_ty, state.file_id, body.span(args))?;
				let range = self.field_range(
					source_ty,
					state,
					FieldIdx::new(at as u32),
					body.span(args),
				)?;
				result.push(
					state
						.push(mir::ExprKind::AggregateGet { local, range }, ty),
				);
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
		prefix: &mut Vec<mir::ExprId>,
	) -> Result<Vec<mir::ExprId>, ()> {
		let written = body.args(elements);
		let mut lowered = Vec::with_capacity(written.len());
		for &element in written {
			lowered.push(self.lower_expr(body, state, element)?);
		}
		match order {
			ElementOrder::InOrder => Ok(lowered),
			ElementOrder::Permuted { .. } => {
				let mut slots: Vec<Option<mir::ExprId>> =
					vec![None; lowered.len()];
				for (at, value) in lowered.into_iter().enumerate() {
					let declared = body.declared_index(order, at);
					let (set, get) = self.spill(state, value);
					prefix.push(set);
					slots[usize::from(declared)] = Some(get);
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
		prefix: &mut Vec<mir::ExprId>,
	) -> Result<Vec<mir::ExprId>, ()> {
		let expr_ty = self.expr_ty(body, state, expr);
		let expected = self
			.aggregate_field_types(expr_ty, state.file_id, body.span(expr))?
			.len();
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
		values: Vec<mir::ExprId>,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let expr_ty = self.expr_ty(body, state, expr);
		let expected = self
			.aggregate_field_types(expr_ty, state.file_id, body.span(expr))?
			.len();
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
			let value_ty = state.ty(value);
			if value_ty == mir::ValueType::Never {
				return Ok(self.sequence(state, prefix, value));
			}
			if value_ty == mir::ValueType::Unit {
				prefix.push(
					state.push(
						mir::ExprKind::Drop { value },
						mir::ValueType::Unit,
					),
				);
				continue;
			}
			let local = self.push_temp_local(state, value_ty);
			prefix.push(state.push(
				mir::ExprKind::LocalSet { local, value },
				mir::ValueType::Unit,
			));
			match value_ty {
				mir::ValueType::Aggregate { aggregate_index } => {
					let scalars =
						self.aggregates.get(aggregate_index).scalars.clone();
					for (at, ty) in scalars.iter().copied().enumerate() {
						slots.push(state.push(
							mir::ExprKind::AggregateGet {
								local,
								range: mir::ScalarRange::new(at as u32, 1),
							},
							ty,
						));
					}
				}
				_ => slots.push(
					state.push(mir::ExprKind::LocalGet { local }, value_ty),
				),
			}
		}
		let value = if ty == mir::ValueType::Unit {
			assert!(slots.is_empty());
			state.push(mir::ExprKind::Noop, ty)
		} else {
			let values = state.list(slots);
			state.push(mir::ExprKind::Aggregate { values }, ty)
		};
		Ok(self.sequence(state, prefix, value))
	}

	/// `object.field`. `AggregateGet` addresses a local, so an object that is
	/// not already one is parked in a fresh temporary, which keeps the
	/// object's evaluation exactly once.
	fn lower_field_access(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		expr: ExprIdx,
		object: ExprIdx,
		field: FieldIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		// A chain rooted in a local needs just one absolute slot selection,
		// rather than a temporary subpack for every source field on the path.
		let mut root = object;
		while let ExprKind::FieldAccess { object, .. } = body.kind(root) {
			root = object;
		}
		if matches!(body.kind(root), ExprKind::Local(_)) {
			let (local, range) = self.local_projection(body, state, expr)?;
			return Ok(
				state.push(mir::ExprKind::AggregateGet { local, range }, ty)
			);
		}
		let object_value = self.lower_expr(body, state, object)?;
		let object_ty = self.expr_ty(body, state, object);
		let range =
			self.field_range(object_ty, state, field, body.span(expr))?;
		if let mir::ExprKind::LocalGet { local } =
			state.mir_body.kind(object_value)
		{
			// The read is replaced by the projection, so its node is left
			// out of the tree; rewrite it into the projection itself.
			state.mir_body.set_kind(
				object_value,
				mir::ExprKind::AggregateGet { local, range },
			);
			state.mir_body.set_ty(object_value, ty);
			return Ok(object_value);
		}
		let object_ty = state.ty(object_value);
		let local = self.push_temp_local(state, object_ty);
		let set = state.push(
			mir::ExprKind::LocalSet {
				local,
				value: object_value,
			},
			mir::ValueType::Unit,
		);
		let get = state.push(mir::ExprKind::AggregateGet { local, range }, ty);
		Ok(self.sequence(state, vec![set], get))
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

	/// Translate one source declaration field of the concrete `ty` into
	/// slots. This map is local
	/// to lowering; the owned MIR contains neither field IDs nor field types.
	fn field_range(
		&mut self,
		ty: TypeIndex,
		state: &FunctionState,
		field: FieldIdx,
		span: TextSpan,
	) -> Result<mir::ScalarRange, ()> {
		let ty = self.normalize_type(ty, state.file_id, span)?;
		self.lower_type(ty, state.file_id, span)?;
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
				let (local, parent) =
					self.local_projection(body, state, object)?;
				let object_ty = self.expr_ty(body, state, object);
				let child = self.field_range(
					object_ty,
					state,
					field,
					body.span(target),
				)?;
				assert!(child.indices().end <= parent.len as usize);
				Ok((
					local,
					mir::ScalarRange::new(
						u32::from(parent.start) + u32::from(child.start),
						child.len,
					),
				))
			}
			_ => {
				self.unsupported(
					state.file_id,
					body.span(target),
					"a non-local assignment target",
				)?;
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
		state: &mut FunctionState,
		target: ExprIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let (local, range) = self.local_projection(body, state, target)?;
		let kind = if matches!(body.kind(target), ExprKind::Local(_)) {
			mir::ExprKind::LocalGet { local }
		} else {
			mir::ExprKind::AggregateGet { local, range }
		};
		Ok(state.push(kind, ty))
	}

	/// Store `value`, already evaluated, into an assignment target. The
	/// target is a local or a flat field range rooted in one.
	fn write_target(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		target: ExprIdx,
		value: mir::ExprId,
	) -> Result<mir::ExprId, ()> {
		let (local, range) = self.local_projection(body, state, target)?;
		let kind = if matches!(body.kind(target), ExprKind::Local(_)) {
			mir::ExprKind::LocalSet { local, value }
		} else {
			mir::ExprKind::AggregateSet {
				local,
				range,
				value,
			}
		};
		Ok(state.push(kind, mir::ValueType::Unit))
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
	) -> Result<mir::ExprId, ()> {
		let target_ty = self.expr_ty(body, state, target);
		let target_ty =
			self.lower_type(target_ty, state.file_id, body.span(target))?;
		let value = self.lower_expr(body, state, value)?;
		if state.ty(value) == mir::ValueType::Never {
			return Ok(value);
		}
		let (set, operand) = self.spill(state, value);
		let read = self.read_target(body, state, target, target_ty)?;
		let Some(kind) = binary_kind(op, read, operand) else {
			self.unsupported(
				state.file_id,
				span,
				"a compound assignment operator in a value position",
			)?;
			unreachable!()
		};
		let result = state.push(kind, target_ty);
		let store = self.write_target(body, state, target, result)?;
		Ok(self.sequence(state, vec![set], store))
	}

	/// `target op= value` through an operator trait's method, the impl's
	/// or, for an abstract target, the one its type selects. The operand runs
	/// first and is read back from a temporary; then the target is read as
	/// the receiver, the method runs, and its result is stored.
	#[allow(clippy::too_many_arguments)]
	fn lower_compound_assign_call(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		target: ExprIdx,
		value: ExprIdx,
		method: FunctionIdx,
		type_args: TypeList,
		span: TextSpan,
	) -> Result<mir::ExprId, ()> {
		let target_ty = self.expr_ty(body, state, target);
		let target_ty =
			self.lower_type(target_ty, state.file_id, body.span(target))?;
		let value = self.lower_expr(body, state, value)?;
		if state.ty(value) == mir::ValueType::Never {
			return Ok(value);
		}
		let (set, operand) = self.spill(state, value);
		let read = self.read_target(body, state, target, target_ty)?;
		let (callee, callee_id) =
			self.callee(state, method, type_args, span)?;
		let (_, callee_params, ..) = self.lower_signature(callee)?;
		if callee_params.len() != 2 {
			self.unsupported(
				state.file_id,
				span,
				"a compound assignment method that is not a binary operator",
			)?;
			unreachable!()
		}
		let call =
			self.build_call(state, callee_id, vec![read, operand], target_ty);
		let store = self.write_target(body, state, target, call)?;
		Ok(self.sequence(state, vec![set], store))
	}

	fn slot_count(&self, ty: mir::ValueType) -> usize {
		match ty {
			mir::ValueType::Unit => 0,
			mir::ValueType::Never => panic!("divergence is not an empty value"),
			mir::ValueType::Aggregate { aggregate_index } => {
				self.aggregates.get(aggregate_index).scalars.len()
			}
			_ => 1,
		}
	}

	/// Run all setup expressions before producing `value`. In particular,
	/// spills must execute even when the final value owns no Wasm slots.
	fn sequence(
		&mut self,
		state: &mut FunctionState,
		mut prefix: Vec<mir::ExprId>,
		value: mir::ExprId,
	) -> mir::ExprId {
		if prefix.is_empty() {
			return value;
		}
		let ty = state.ty(value);
		prefix.push(value);
		let statements = state.list(prefix);
		state.push(mir::ExprKind::Sequence { statements }, ty)
	}

	/// `&&` and `||` branch on the left operand, so the right one runs only
	/// when it decides the result: `a && b` is `if a { b } else { false }`,
	/// and `a || b` is `if a { true } else { b }`. The left operand is
	/// evaluated exactly once, before either branch.
	fn lower_short_circuit(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		op: BinaryOp,
		lhs: ExprIdx,
		rhs: ExprIdx,
	) -> Result<mir::ExprId, ()> {
		// A diverging operand is `!`, which fits the `Bool` expectation, so
		// it never produces a value for the branch.
		debug_assert!(matches!(
			body.ty(lhs),
			TypeIndex::BOOL | TypeIndex::NEVER
		));
		let condition = self.lower_expr(body, state, lhs)?;
		let right = self.lower_expr(body, state, rhs)?;
		let (then, otherwise) = match op {
			BinaryOp::And => (right, state.boolean(false)),
			BinaryOp::Or => (state.boolean(true), right),
			_ => unreachable!("only logical operators short-circuit"),
		};
		Ok(state.push(
			mir::ExprKind::IfElse {
				condition,
				then,
				otherwise: Some(otherwise),
			},
			mir::ValueType::Bool,
		))
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
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		let ty = self.normalize_type(ty, file_id, span)?;
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
				self.lower_type(repr, file_id, span)?
			}
			Type::Tuple { .. } | Type::Struct { .. } => {
				return self.lower_aggregate_type(ty, file_id, span);
			}
			Type::Pointer { .. } | Type::Array { .. } | Type::Slice { .. } => {
				self.unsupported(
					file_id,
					span,
					"a memory-backed type (the memory checkpoint)",
				)?;
				unreachable!()
			}
			// A function item is its own zero-sized type: calling it names
			// its function, so the value carries nothing.
			Type::Function { .. } => mir::ValueType::Unit,
			// A global's handle names it in its type; the value is nothing.
			Type::Global { .. } => mir::ValueType::Unit,
			Type::Funcref | Type::TypedFuncref { .. } => {
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

	/// `ty`, which has no parameter, with every projection and constant in
	/// it reduced. A parameter-free type means the same in every scope, so
	/// this asks the root scope, as the solver itself keys such a request.
	fn normalize_type(
		&mut self,
		ty: TypeIndex,
		file_id: FileId,
		span: TextSpan,
	) -> Result<TypeIndex, ()> {
		debug_assert!(
			!self.context.types.has_param(ty),
			"lowering normalizes concrete types only"
		);
		match self.context.normalize(
			TypeEnvIdx::ROOT,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		) {
			Ok(ty) => Ok(ty),
			Err(_) => {
				self.unsupported(
					file_id,
					span,
					"a type that does not normalize",
				)?;
				unreachable!()
			}
		}
	}

	/// Materialize one concrete type's flat representation, without a second
	/// structural interner. Memory layout is copied from TIR when available.
	fn lower_aggregate_type(
		&mut self,
		ty: TypeIndex,
		file_id: FileId,
		span: TextSpan,
	) -> Result<mir::ValueType, ()> {
		if let Some(representation) = self.aggregate_types.get(&ty) {
			return Ok(representation.ty);
		}

		let field_types = self.aggregate_field_types(ty, file_id, span)?;
		let mut scalars = Vec::new();
		let mut fields = Vec::with_capacity(field_types.len());
		for field in field_types {
			let field = self.lower_type(field, file_id, span)?;
			let start = scalars.len();
			match field {
				mir::ValueType::Unit => {}
				mir::ValueType::Never => {
					self.unsupported(
						file_id,
						span,
						"an uninhabited aggregate value",
					)?;
				}
				mir::ValueType::Aggregate { aggregate_index } => scalars
					.extend_from_slice(
						&self.aggregates.get(aggregate_index).scalars,
					),
				scalar => scalars.push(scalar),
			}
			// Every field passed this check when it was lowered, so this
			// stops a doubling chain after one step past the limit, before
			// `memory_values` flattens the type a second time.
			if scalars.len() > SLOT_LIMIT {
				let name = self.context.type_formatter().display_type(ty);
				self.context.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::SlotLimit.code())
						.with_message(format!(
							"the type `{name}` is too large to lower"
						))
						.with_label(
							Label::primary(file_id, span).with_message(
								"a value of this type is used here",
							),
						)
						.with_note(format!(
							"a value is held as one Wasm value per scalar it \
							 contains, and the limit is {SLOT_LIMIT} for one type"
						)),
				);
				return Err(());
			}
			fields.push(mir::ScalarRange::new(
				start.try_into().unwrap(),
				(scalars.len() - start).try_into().unwrap(),
			));
		}

		let lowered = if scalars.is_empty() {
			mir::ValueType::Unit
		} else {
			let memory = match self.context.memory_values(TypeEnvIdx::ROOT, ty)
			{
				Ok(Some((layout, values))) => {
					assert_eq!(
						values.len(),
						scalars.len(),
						"TIR stack and memory slot counts agree"
					);
					Some(mir::AggregateMemory {
						layout: mir::Layout {
							size: layout.size,
							align: layout.align,
						},
						offsets: values
							.iter()
							.map(|&(_, offset)| offset)
							.collect(),
					})
				}
				Ok(None) => None,
				Err(_) => {
					self.unsupported(
						file_id,
						span,
						"an aggregate whose memory layout failed",
					)?;
					unreachable!()
				}
			};
			let aggregate_index =
				self.aggregates.push(scalars.into_boxed_slice(), memory);
			mir::ValueType::Aggregate { aggregate_index }
		};
		self.aggregate_types.insert(
			ty,
			AggregateLowering {
				ty: lowered,
				fields: fields.into_boxed_slice(),
			},
		);
		Ok(lowered)
	}

	/// A tuple's element types, or a struct's field types substituted with
	/// its type arguments, both in declaration order.
	fn aggregate_field_types(
		&mut self,
		ty: TypeIndex,
		file_id: FileId,
		span: TextSpan,
	) -> Result<Vec<TypeIndex>, ()> {
		let ty = self.normalize_type(ty, file_id, span)?;
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

/// The MIR node for the primitive operator `op`, or `None` for an
/// assignment operator, which has no value.
fn binary_kind(
	op: BinaryOp,
	lhs: mir::ExprId,
	rhs: mir::ExprId,
) -> Option<mir::ExprKind> {
	let binary = |op| mir::ExprKind::Binary { op, lhs, rhs };
	let compare = |op| mir::ExprKind::Compare { op, lhs, rhs };
	Some(match op {
		BinaryOp::Add => binary(mir::BinaryOp::Add),
		BinaryOp::Sub => binary(mir::BinaryOp::Sub),
		BinaryOp::Mul => binary(mir::BinaryOp::Mul),
		BinaryOp::Div => binary(mir::BinaryOp::Div),
		BinaryOp::Rem => binary(mir::BinaryOp::Rem),
		BinaryOp::BitAnd => binary(mir::BinaryOp::BitAnd),
		BinaryOp::BitOr => binary(mir::BinaryOp::BitOr),
		BinaryOp::BitXor => binary(mir::BinaryOp::BitXor),
		BinaryOp::LeftShift => binary(mir::BinaryOp::Shl),
		BinaryOp::RightShift => binary(mir::BinaryOp::Shr),
		BinaryOp::Eq => compare(mir::CompareOp::Eq),
		BinaryOp::NotEq => compare(mir::CompareOp::Ne),
		BinaryOp::Less => compare(mir::CompareOp::Lt),
		BinaryOp::LessEq => compare(mir::CompareOp::Le),
		BinaryOp::Greater => compare(mir::CompareOp::Gt),
		BinaryOp::GreaterEq => compare(mir::CompareOp::Ge),
		// `&&`/`||` are lowered as `IfElse` branches (`lower_short_circuit`).
		BinaryOp::And | BinaryOp::Or => {
			unreachable!("a logical operator short-circuits")
		}
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

#[cfg(test)]
mod tests {
	use super::*;

	/// Every direct call in `mir`, across its functions.
	fn call_count(mir: &mir::MIR) -> usize {
		mir.functions
			.iter()
			.filter_map(|f| f.code())
			.map(|code| code.callees().count())
			.sum()
	}

	/// Check, lower, inline, encode, and instantiate `source`, returning the
	/// live store and instance for calling exports. Every program run here
	/// goes through the inliner, as a built one does.
	fn instantiate(source: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		let Some(mut mir) = mir else {
			panic!(
				"the checkpoint must lower: {:?}",
				diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
			)
		};
		crate::mir::inline::run(&mut mir, crate::mir::inline::Policy::DEFAULT);
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
		let mir = crate::tir::build(&mut graph).1.expect("trap must expand");
		assert_eq!(mir.functions.len(), 1);
		let function = mir.code(mir::FunctionId::new(0));
		assert_eq!(function.callees().count(), 0);
		assert!(mir.imports.is_empty());
		let mir::ExprKind::Sequence { statements } =
			function.body.kind(function.root)
		else {
			panic!("expected a sequence")
		};
		let last = *function.body.list(statements).last().unwrap();
		assert!(matches!(
			function.body.kind(last),
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
			.1
			.expect("scalar intrinsics must expand");
		assert_eq!(
			mir.functions.len(),
			6,
			"only the ordinary callee gets a body"
		);
		assert_eq!(call_count(&mir), 1);
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
	fn transmute_keeps_the_operands_signedness_and_gives_its_own() {
		// `a / b` stays an unsigned division although its result is read as
		// an `i32`; the transmuted operand of `/ 2` and `>> 1` divides and
		// shifts as the target type.
		let source = r#"
			func quotient(a: u32, b: u32) -> i32 { transmute::<u32, i32>(a / b) }
			func signed_half(a: u32) -> i32 { transmute::<u32, i32>(a) / 2 }
			func unsigned_shift(x: i32) -> u32 { transmute::<i32, u32>(x) >> 1 }
			export {
				quotient as "quotient",
				signed_half as "signed_half",
				unsigned_shift as "unsigned_shift",
			}
		"#;
		let (mut store, instance) = instantiate(source);
		let quotient = instance
			.get_typed_func::<(u32, u32), i32>(&mut store, "quotient")
			.unwrap();
		assert_eq!(
			quotient.call(&mut store, (u32::MAX - 1, 2)).unwrap(),
			i32::MAX
		);
		let signed_half = instance
			.get_typed_func::<u32, i32>(&mut store, "signed_half")
			.unwrap();
		assert_eq!(signed_half.call(&mut store, u32::MAX - 1).unwrap(), -1);
		let unsigned_shift = instance
			.get_typed_func::<i32, u32>(&mut store, "unsigned_shift")
			.unwrap();
		assert_eq!(unsigned_shift.call(&mut store, -2).unwrap(), u32::MAX >> 1);
	}

	#[test]
	fn transmute_converts_between_a_scalar_and_a_one_slot_aggregate() {
		let source = r#"
			func round_trip(c: u32) -> u32 {
				local ch: Char = transmute(c);
				transmute(ch)
			}
			func codepoint() -> u32 { transmute::<Char, u32>('a') }
			export { round_trip as "round_trip", codepoint as "codepoint" }
		"#;
		let (mut store, instance) = instantiate(source);
		let round_trip = instance
			.get_typed_func::<u32, u32>(&mut store, "round_trip")
			.unwrap();
		assert_eq!(round_trip.call(&mut store, 0x20AC).unwrap(), 0x20AC);
		let codepoint = instance
			.get_typed_func::<(), u32>(&mut store, "codepoint")
			.unwrap();
		assert_eq!(codepoint.call(&mut store, ()).unwrap(), 97);
	}

	#[test]
	fn transmute_regroups_aggregates_with_the_same_slots() {
		// Declaration order, with zero-sized parts dropped, is both the
		// `StackValue::Repr` order and MIR's slot order.
		let source = r#"
			struct Meters(m: u32);
			struct Pair(a: Meters, unit: (), b: u32);
			func regroup(x: u32, y: u32) -> u32 {
				local Pair({ a: Meters(a), b, .. }) = transmute::<(u32, u32), Pair>((x, y));
				a * 10 + b
			}
			func flatten(p: Pair) -> (u32, u32) { transmute(p) }
			func make() -> (u32, u32) { flatten(Pair(Meters(5), (), 6)) }
			export { regroup as "regroup", make as "make" }
		"#;
		let (mut store, instance) = instantiate(source);
		let regroup = instance
			.get_typed_func::<(u32, u32), u32>(&mut store, "regroup")
			.unwrap();
		assert_eq!(regroup.call(&mut store, (3, 4)).unwrap(), 34);
		let make = instance
			.get_typed_func::<(), (u32, u32)>(&mut store, "make")
			.unwrap();
		assert_eq!(make.call(&mut store, ()).unwrap(), (5, 6));
	}

	#[test]
	fn std_impls_built_on_transmute_run() {
		// `Bool`'s `!` and the narrow-integer operators are std impls over
		// `transmute`d `i32` instructions.
		let source = r#"
			func not(b: u32) -> u32 { if !(b == 0) { 1 } else { 2 } }
			func narrow(a: i8, b: i8) -> i8 { a.div(b) }
			export { not as "not", narrow as "narrow" }
		"#;
		let (mut store, instance) = instantiate(source);
		let not = instance
			.get_typed_func::<u32, u32>(&mut store, "not")
			.unwrap();
		assert_eq!(not.call(&mut store, 0).unwrap(), 2);
		assert_eq!(not.call(&mut store, 7).unwrap(), 1);
		let narrow = instance
			.get_typed_func::<(i32, i32), i32>(&mut store, "narrow")
			.unwrap();
		assert_eq!(narrow.call(&mut store, (-6, 2)).unwrap(), -3);
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
				r#"use std::trap as provided; export { provided as "trap" }"#,
				"requires a wrapper",
			),
			(
				r#"memory heap: u32; func run() -> u32 { std::size_of::<i32, heap>() } export { run as "run" }"#,
				"compiler intrinsic SizeOf",
			),
		] {
			let mut graph = crate::tir::signatures::tests::source_graph(source);
			let (diagnostics, mir) = crate::tir::build(&mut graph);
			assert!(
				mir.is_none(),
				"unsupported implementation must not emit MIR"
			);
			assert!(
				diagnostics.iter().any(|d| d.message.contains(message)
					&& d.code.as_deref()
						== Some(DiagnosticCode::UnsupportedExpression.code())
					&& !d.labels.is_empty()),
				"expected {message:?}, got {diagnostics:#?}"
			);
		}
	}

	/// Three imports under one Wasm name: two with the same Wasm type, one
	/// with another. Each is its own wx function.
	const OVERLOADED_IMPORTS: &str = r#"
		import "host" as host { func log(value: i32); }
		import "host" as host_2 { func log(value: i64); }
		import "host" as host_3 { func log(value: u32); }
		func run() {
			host::log(1);
			host_2::log(2);
			host_3::log(3);
		}
		export { run as "run" }
	"#;

	#[test]
	fn each_imported_function_is_its_own_item_with_its_own_import_entry() {
		let mut graph =
			crate::tir::signatures::tests::source_graph(OVERLOADED_IMPORTS);
		let mir = crate::tir::build(&mut graph).1.expect("imports lower");
		assert_eq!(mir.imports.len(), 3, "never merged by name in MIR");
		mir.verify_imports().unwrap();
		for import in &mir.imports {
			assert_eq!(graph.strings.resolve(import.module), Some("host"));
			assert_eq!(graph.strings.resolve(import.name), Some("log"));
			let mir::Item::Function(id) = import.item else {
				panic!("only functions are imported")
			};
			assert!(mir.function(id).code().is_none());
		}
		let distinct: std::collections::HashSet<_> = mir
			.imports
			.iter()
			.map(|import| match import.item {
				mir::Item::Function(id) => id,
				_ => unreachable!(),
			})
			.collect();
		assert_eq!(distinct.len(), 3);
		assert_eq!(call_count(&mir), 3);
	}

	#[test]
	fn codegen_gives_imports_with_the_same_names_and_wasm_type_one_entry() {
		let mut graph =
			crate::tir::signatures::tests::source_graph(OVERLOADED_IMPORTS);
		let mir = crate::tir::build(&mut graph).1.expect("imports lower");
		let bytes = crate::codegen::Builder::build(&mir, &graph.strings)
			.expect("lowered MIR must encode")
			.encode();
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, &bytes)
			.expect("lowered MIR must be valid Wasm");
		// `log(i32)` and `log(u32)` are both `(param i32)` to the host.
		let imports: Vec<String> = module
			.imports()
			.map(|import| {
				format!(
					"{}.{}: {:?}",
					import.module(),
					import.name(),
					import.ty()
				)
			})
			.collect();
		assert_eq!(imports.len(), 2, "{imports:#?}");
		let mut store = wasmtime::Store::new(&engine, Vec::<i64>::new());
		let narrow = wasmtime::Func::wrap(
			&mut store,
			|mut caller: wasmtime::Caller<'_, Vec<i64>>, value: i32| {
				caller.data_mut().push(i64::from(value));
			},
		);
		let wide = wasmtime::Func::wrap(
			&mut store,
			|mut caller: wasmtime::Caller<'_, Vec<i64>>, value: i64| {
				caller.data_mut().push(-value);
			},
		);
		let instance = wasmtime::Instance::new(
			&mut store,
			&module,
			&[narrow.into(), wide.into()],
		)
		.expect("one host function per import entry");
		instance
			.get_typed_func::<(), ()>(&mut store, "run")
			.unwrap()
			.call(&mut store, ())
			.unwrap();
		assert_eq!(store.data(), &[1, -2, 3]);
	}

	#[test]
	fn a_mutable_global_is_read_and_written_through_its_traits() {
		let source = r#"
			global mut counter: u32 = 5;
			func bump() -> u32 {
				counter.set(counter.get() + 1);
				counter.get()
			}
			export { bump as "bump" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("globals lower");
		let [global] = mir.globals.as_slice() else {
			panic!("one global")
		};
		assert!(matches!(global.mutability, mir::Mutability::Mutable));
		assert!(matches!(
			global.origin,
			mir::Origin::Defined(mir::ConstInit::Int(5))
		));
		let (mut store, instance) = instantiate(source);
		let bump = instance
			.get_typed_func::<(), u32>(&mut store, "bump")
			.unwrap();
		assert_eq!(bump.call(&mut store, ()).unwrap(), 6);
		assert_eq!(bump.call(&mut store, ()).unwrap(), 7);
	}

	#[test]
	fn a_one_value_newtype_global_is_held_as_its_scalar() {
		let source = r#"
			struct Meters(u32);
			global mut length: Meters = Meters(3);
			func double() -> u32 {
				local Meters(x) = length.get();
				length.set(Meters(x * 2));
				local Meters(y) = length.get();
				y
			}
			export { double as "double" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("globals lower");
		assert_eq!(mir.globals[0].ty, mir::ValueType::U32);
		let (mut store, instance) = instantiate(source);
		let double = instance
			.get_typed_func::<(), u32>(&mut store, "double")
			.unwrap();
		assert_eq!(double.call(&mut store, ()).unwrap(), 6);
		assert_eq!(double.call(&mut store, ()).unwrap(), 12);
	}

	#[test]
	fn an_exported_global_holds_its_compile_time_value() {
		let source = r#"
			const BASE: i32 = 40;
			global answer: i32 = BASE + 2;
			global ratio: f64 = 0.5;
			global unused: u32 = 1;
			export { answer as "answer", ratio as "ratio" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("globals lower");
		assert_eq!(
			mir.globals.len(),
			2,
			"a global nothing names is not emitted"
		);
		let (mut store, instance) = instantiate(source);
		let answer = instance.get_global(&mut store, "answer").unwrap();
		assert_eq!(answer.get(&mut store).i32(), Some(42));
		assert_eq!(answer.ty(&store).mutability(), wasmtime::Mutability::Const);
		let ratio = instance.get_global(&mut store, "ratio").unwrap();
		assert_eq!(ratio.get(&mut store).f64(), Some(0.5));
	}

	#[test]
	fn an_imported_global_is_an_import_entry_the_host_fills() {
		let source = r#"
			import "env" as env { global base: i32; }
			func read() -> i32 { env::base.get() + 1 }
			export { read as "read" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mut mir = crate::tir::build(&mut graph).1.expect("globals lower");
		let [import] = mir.imports.as_slice() else {
			panic!("one import entry")
		};
		assert_eq!(graph.strings.resolve(import.module), Some("env"));
		assert_eq!(graph.strings.resolve(import.name), Some("base"));
		assert_eq!(import.item, mir::Item::Global(mir::GlobalId::new(0)));
		mir.verify_imports().unwrap();
		crate::mir::inline::run(&mut mir, crate::mir::inline::Policy::DEFAULT);
		let bytes = crate::codegen::Builder::build(&mir, &graph.strings)
			.expect("lowered MIR must encode")
			.encode();
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, &bytes).unwrap();
		let mut store = wasmtime::Store::new(&engine, ());
		let base = wasmtime::Global::new(
			&mut store,
			wasmtime::GlobalType::new(
				wasmtime::ValType::I32,
				wasmtime::Mutability::Const,
			),
			wasmtime::Val::I32(41),
		)
		.unwrap();
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[base.into()])
				.unwrap();
		let read = instance
			.get_typed_func::<(), i32>(&mut store, "read")
			.unwrap();
		assert_eq!(read.call(&mut store, ()).unwrap(), 42);
	}

	#[test]
	fn a_generic_function_reads_the_global_its_argument_names() {
		let source = r#"
			global small: i8 = -3;
			global flag: Bool = True;
			global mut total: i32 = 10;
			func read<G: Global>(g: G) -> G::Value { g.get() }
			func run() -> i32 {
				total.set(read(total) + widen(read(small)));
				if read(flag) { read(total) } else { 0 }
			}
			// A narrow signed value is held sign-extended in its `i32`.
			func widen(x: i8) -> i32 { transmute(x) }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 7);
		assert_eq!(run.call(&mut store, ()).unwrap(), 4);
	}

	#[test]
	fn a_global_initializer_must_be_a_constant_expression() {
		let source = r#"
			func one() -> u32 { 1 }
			global g: u32 = one();
			func read() -> u32 { g.get() }
			export { read as "read" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		assert!(mir.is_none());
		crate::testing::DiagnosticView::new(
			"build",
			&diagnostics,
			&graph.files,
		)
		.assert_error(DiagnosticCode::NonConstantGlobalInitializer);
	}

	#[test]
	fn lowers_an_exported_scalar_add_to_runnable_mir() {
		let source = r#"
            func add(a: i32, b: i32) -> i32 { a + b }
            export { add as "add" }
        "#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph)
			.1
			.expect("a scalar add must lower");
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
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		assert!(
			mir.is_none(),
			"an aggregate constant pattern has no equality"
		);
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
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		assert!(mir.is_none(), "memory types have no lowering yet");
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
		let mir = crate::tir::build(&mut graph)
			.1
			.expect("nested updates must lower");
		assert!(mir.aggregates.iter().all(|pack| pack.scalars.iter().all(
			|ty| !matches!(
				ty,
				mir::ValueType::Aggregate { .. }
					| mir::ValueType::Unit
					| mir::ValueType::Never
			)
		)));
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), (i32, i64, i32)>(&mut store, "run")
			.unwrap();
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
		let run = instance
			.get_typed_func::<(), (i32, i32)>(&mut store, "run")
			.unwrap();
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
		let mir = crate::tir::build(&mut graph).1.unwrap();
		let layouts: Vec<_> = mir
			.aggregates
			.iter()
			.map(|pack| {
				assert_eq!(
					pack.scalars.as_ref(),
					[
						mir::ValueType::U8,
						mir::ValueType::I64,
						mir::ValueType::U8
					]
				);
				pack.memory.as_ref().unwrap().offsets.to_vec()
			})
			.collect();
		assert!(layouts.contains(&vec![8, 0, 9]));
		assert!(layouts.contains(&vec![0, 8, 16]));
		let (mut store, instance) = instantiate(source);
		for name in ["sorted", "fixed"] {
			let identity = instance
				.get_typed_func::<(i32, i64, i32), (i32, i64, i32)>(
					&mut store, name,
				)
				.unwrap();
			assert_eq!(
				identity.call(&mut store, (7, 1 << 40, 9)).unwrap(),
				(7, 1 << 40, 9)
			);
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
		let run = instance
			.get_typed_func::<(), i32>(&mut store, "run")
			.unwrap();
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
			let run = instance
				.get_typed_func::<(), i32>(&mut store, "run")
				.unwrap();
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
		let mir = crate::tir::build(&mut graph)
			.1
			.expect("the aggregate must lower");

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
	fn every_instance_of_an_inline_function_is_flagged_inline() {
		let source = r#"
			#[inline]
			func twice<T: Add>(x: T) -> T { x + x }
			func small(a: u32) -> u32 { twice(a) }
			func big(b: u64) -> u64 { twice(b) }
			export { small as "small", big as "big" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("the source lowers");
		// `small`, `big`, `twice` for `u32` and `u64`, and std's `#[inline]`
		// `add` for each.
		assert_eq!(mir.functions.len(), 6);
		assert_eq!(mir.function_flags.len(), mir.functions.len());
		let exported: Vec<mir::FunctionId> = mir
			.exports
			.iter()
			.map(|export| match export.item {
				mir::Item::Function(id) => id,
				_ => unreachable!("only functions are exported"),
			})
			.collect();
		for (id, _) in mir.functions_with_ids() {
			assert_eq!(
				mir.flags(id).contains(mir::FunctionFlags::INLINE),
				!exported.contains(&id),
				"{id:?}"
			);
		}
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
	fn a_generic_function_has_one_instance_per_argument_list() {
		// Inferred and written arguments name the same instance.
		let source = r#"
			func id<T>(x: T) -> T { x }
			func run(a: i32, b: i64) -> (i32, i64) {
				(id(a) + id::<i32>(a), id(b))
			}
			export { run as "run" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("`id` must lower");
		assert_eq!(mir.functions.len(), 3, "`run`, `id<i32>` and `id<i64>`");
		drop(graph);
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, i64), (i32, i64)>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (4, 9)).unwrap(), (8, 9));
	}

	#[test]
	fn a_generic_callee_receives_its_callers_arguments() {
		// `pair`'s call of `id` names `id<T>`, which is `id<u8>` and
		// `id<Wrap<u32>>` in the two instances of `pair`.
		let source = r#"
			struct Wrap<T>(value: T);
			func id<T>(x: T) -> T { x }
			func pair<T>(x: T) -> (T, T) { (id(x), id::<T>(x)) }
			func run(a: u8, b: u32) -> u32 {
				local (c, d) = pair(a);
				local (Wrap(e), Wrap(f)) = pair(Wrap(b));
				transmute::<u8, u32>(c) + transmute::<u8, u32>(d) + e * f
			}
			export { run as "run" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("`pair` must lower");
		assert_eq!(mir.functions.len(), 5, "`run`, two `pair`s, two `id`s");
		drop(graph);
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(i32, u32), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (2, 3)).unwrap(), 13);
	}

	#[test]
	fn a_generic_impl_method_runs_on_a_concrete_type() {
		let source = r#"
			struct Pair<T>(a: T, b: T);
			impl<T> Pair<T> {
				pub func new(a: T, b: T) -> Pair<T> { Pair(a, b) }
				pub func swap(self: Self) -> Pair<T> { Pair(self.b, self.a) }
			}
			func run(x: u32, y: u32) -> u32 {
				local Pair(a, b) = Pair::new(x, y).swap();
				a * 10 + b
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(u32, u32), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (1, 2)).unwrap(), 21);
	}

	#[test]
	fn a_recursive_generic_call_with_the_same_arguments_is_one_instance() {
		let source = r#"
			func count<T>(x: T, n: u32) -> u32 {
				if n == 0 { 0 } else { count(x, n - 1) + 1 }
			}
			func run(n: u32) -> u32 { count((1: u8), n) }
			export { run as "run" }
		"#;
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let mir = crate::tir::build(&mut graph).1.expect("`count` must lower");
		assert_eq!(mir.functions.len(), 2);
		drop(graph);
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<u32, u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 5).unwrap(), 5);
	}

	#[test]
	fn an_operator_on_a_type_parameter_runs_each_instances_impl() {
		let source = r#"
			func sum<T: Add>(a: T, b: T) -> T { a + b }
			func small(x: u32) -> u32 { sum(x, 1) }
			func large(x: u64) -> u64 { sum(x, 2) }
			func float(x: f32) -> f32 { sum(x, 0.5) }
			export { small as "small", large as "large", float as "float" }
		"#;
		let (mut store, instance) = instantiate(source);
		let small = instance
			.get_typed_func::<u32, u32>(&mut store, "small")
			.unwrap();
		let large = instance
			.get_typed_func::<u64, u64>(&mut store, "large")
			.unwrap();
		let float = instance
			.get_typed_func::<f32, f32>(&mut store, "float")
			.unwrap();
		assert_eq!(small.call(&mut store, 4).unwrap(), 5);
		assert_eq!(large.call(&mut store, 1 << 40).unwrap(), (1 << 40) + 2);
		assert_eq!(float.call(&mut store, 1.0).unwrap(), 1.5);
	}

	#[test]
	fn a_trait_method_on_a_type_parameter_runs_the_impl_its_type_selects() {
		let source = r#"
			trait Shape { func area(self: Self) -> u32; }
			struct Square(side: u32);
			struct Rect(w: u32, h: u32);
			impl Shape for Square {
				func area(self: Self) -> u32 {
					local Square(s) = self;
					s * s
				}
			}
			impl Shape for Rect {
				func area(self: Self) -> u32 {
					local Rect(w, h) = self;
					w * h
				}
			}
			func twice<S: Shape>(s: S) -> u32 { s.area() + S::area(s) }
			func run(a: u32, b: u32) -> u32 {
				twice(Square(a)) * 1000 + twice(Rect(a, b))
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(u32, u32), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (3, 4)).unwrap(), 18 * 1000 + 24);
	}

	#[test]
	fn an_inherited_default_runs_for_a_concrete_and_an_abstract_self() {
		let source = r#"
			trait Counter {
				func base(self: Self) -> u32;
				func next(self: Self) -> u32 { self.base() + 1 }
			}
			struct A(v: u32);
			struct B(v: u32);
			impl Counter for A {
				func base(self: Self) -> u32 { local A(v) = self; v }
			}
			impl Counter for B {
				func base(self: Self) -> u32 { local B(v) = self; v }
				func next(self: Self) -> u32 { self.base() + 100 }
			}
			func through<C: Counter>(c: C) -> u32 { c.next() }
			func direct(x: u32) -> u32 { A(x).next() }
			func generic(x: u32) -> u32 { through(A(x)) * 1000 + through(B(x)) }
			export { direct as "direct", generic as "generic" }
		"#;
		let (mut store, instance) = instantiate(source);
		let direct = instance
			.get_typed_func::<u32, u32>(&mut store, "direct")
			.unwrap();
		let generic = instance
			.get_typed_func::<u32, u32>(&mut store, "generic")
			.unwrap();
		assert_eq!(direct.call(&mut store, 1).unwrap(), 2);
		assert_eq!(generic.call(&mut store, 1).unwrap(), 2 * 1000 + 101);
	}

	#[test]
	fn std_s_inherited_ne_runs_on_a_type_parameter() {
		let source = r#"
			func differ<T: PartialEq>(a: T, b: T) -> Bool { a != b }
			func run(a: u32, b: u32) -> u32 {
				if differ(a, b) { 1 } else { 0 }
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(u32, u32), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (1, 1)).unwrap(), 0);
		assert_eq!(run.call(&mut store, (1, 2)).unwrap(), 1);
	}

	#[test]
	fn an_associated_constant_is_read_per_instance() {
		let source = r#"
			trait Sized { const SIZE: u32; }
			struct Small();
			struct Big();
			impl Sized for Small { const SIZE: u32 = 4; }
			impl Sized for Big { const SIZE: u32 = 64; }
			func size<T: Sized>() -> u32 { T::SIZE }
			func run() -> u32 { size::<Small>() + size::<Big>() * 100 + Big::SIZE }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, ()).unwrap(), 4 + 6400 + 64);
	}

	#[test]
	fn a_compound_assignment_on_a_type_parameter_runs_its_impl() {
		let source = r#"
			func triple<T: Add>(x: T) -> T {
				local mut acc = x;
				acc += x;
				acc += x;
				acc
			}
			func run(x: i64) -> i64 { triple(x) }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<i64, i64>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, -7).unwrap(), -21);
	}

	#[test]
	fn a_generic_impl_method_dispatches_on_its_impl_s_parameter() {
		let source = r#"
			struct Pair<T>(a: T, b: T);
			impl<T: Add> Pair<T> {
				pub func total(self: Self) -> T {
					local Pair(a, b) = self;
					a + b
				}
			}
			func run(x: u32, y: u32) -> u32 { Pair(x, y).total() }
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<(u32, u32), u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, (2, 5)).unwrap(), 7);
	}

	#[test]
	fn a_function_item_value_is_called_as_its_function() {
		let source = r#"
			func double(x: u32) -> u32 { x * 2 }
			func add(a: u32, b: u32) -> u32 { a + b }
			func apply<F: Call where { Args = u32, Result = u32 }>(f: F, x: u32) -> u32 {
				f(x)
			}
			func run(x: u32) -> u32 {
				local g = add;
				apply(double, x) + g(x, 1)
			}
			export { run as "run" }
		"#;
		let (mut store, instance) = instantiate(source);
		let run = instance
			.get_typed_func::<u32, u32>(&mut store, "run")
			.unwrap();
		assert_eq!(run.call(&mut store, 5).unwrap(), 10 + 6);
	}

	/// The diagnostics with `code` that building `source` reports, which must
	/// emit no MIR.
	fn build_reports(
		source: &str,
		code: DiagnosticCode,
	) -> Vec<Diagnostic<FileId>> {
		let mut graph = crate::tir::signatures::tests::source_graph(source);
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		assert!(mir.is_none(), "a failed instantiation emits no MIR");
		diagnostics
			.into_iter()
			.filter(|d| d.code.as_deref() == Some(code.code()))
			.collect()
	}

	#[test]
	fn a_doubling_type_reaches_the_slot_limit_first() {
		// Each level is one interned type and twice the values of the last,
		// so the slot limit stops it at about sixteen levels, long before the
		// recursion limit would.
		let source = r#"
			func grow<T>(x: T, n: u32) -> u32 {
				if n == 0 { 0 } else { grow((x, x), n - 1) }
			}
			func run(n: u32) -> u32 { grow((1: u8), n) }
			export { run as "run" }
		"#;
		let reports = build_reports(source, DiagnosticCode::SlotLimit);
		assert_eq!(reports.len(), 1, "{reports:#?}");
		assert_eq!(
			reports[0].severity,
			codespan_reporting::diagnostic::Severity::Error
		);
		assert!(
			reports[0].message.starts_with("the type `((((")
				&& reports[0].message.ends_with(")` is too large to lower")
				&& reports[0].message.contains("...)"),
			"{}",
			reports[0].message
		);
		assert!(
			build_reports(source, DiagnosticCode::RecursionLimit).is_empty()
		);
	}

	#[test]
	fn a_doubling_zero_sized_type_reaches_the_recursion_limit() {
		// No slots, so only the recursion limit stops it, and its message
		// names a type of 2^128 leaves by printing only the start of it.
		let source = r#"
			func grow<T>(x: T, n: u32) -> u32 {
				if n == 0 { 0 } else { grow((x, x), n - 1) }
			}
			func run(n: u32) -> u32 { grow((), n) }
			export { run as "run" }
		"#;
		let reports = build_reports(source, DiagnosticCode::RecursionLimit);
		assert_eq!(reports.len(), 1, "{reports:#?}");
		assert!(reports[0].message.len() < 200, "{}", reports[0].message);
		assert!(
			reports[0].message.contains("...)"),
			"{}",
			reports[0].message
		);
	}

	#[test]
	fn unbounded_polymorphic_recursion_reaches_the_recursion_limit() {
		// Directly, and through a second function, every call wraps its
		// argument once more, so no instance repeats.
		for source in [
			r#"
				struct Wrap<T>(value: T);
				func grow<T>(x: T, n: u32) -> u32 {
					if n == 0 { 0 } else { grow(Wrap(x), n - 1) }
				}
				func run(n: u32) -> u32 { grow((1: u8), n) }
				export { run as "run" }
			"#,
			r#"
				struct Wrap<T>(value: T);
				func ping<T>(x: T, n: u32) -> u32 {
					if n == 0 { 0 } else { pong(Wrap(x), n - 1) }
				}
				func pong<T>(x: T, n: u32) -> u32 { ping(x, n) }
				func run(n: u32) -> u32 { ping((1: u8), n) }
				export { run as "run" }
			"#,
		] {
			let mut graph = crate::tir::signatures::tests::source_graph(source);
			let (diagnostics, mir) = crate::tir::build(&mut graph);
			assert!(mir.is_none(), "an unbounded instantiation emits no MIR");
			let reports: Vec<_> = diagnostics
				.iter()
				.filter(|d| {
					d.code.as_deref()
						== Some(DiagnosticCode::RecursionLimit.code())
				})
				.collect();
			assert_eq!(reports.len(), 1, "{diagnostics:#?}");
			let report = reports[0];
			assert_eq!(
				report.severity,
				codespan_reporting::diagnostic::Severity::Error
			);
			assert!(
				report.message.starts_with(
					"reached the recursion limit while instantiating `"
				) && report.message.contains("Wrap<Wrap<"),
				"{}",
				report.message
			);
			assert_eq!(report.labels.len(), 2);
		}
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
		let (diagnostics, mir) = crate::tir::build(&mut graph);
		assert!(mir.is_none(), "a float constant pattern has no equality");
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
		let mir = crate::tir::build(&mut graph)
			.1
			.expect("`continue` must lower");
		let function = mir.code(mir::FunctionId::new(0));
		let body = &function.body;
		let only = |list: mir::ExprList| -> mir::ExprId { body.list(list)[0] };
		let mut at = function.root;
		if let mir::ExprKind::Sequence { statements } = body.kind(at) {
			at = only(statements);
		}
		let mir::ExprKind::Loop {
			label: outer,
			body: outer_body,
		} = body.kind(at)
		else {
			panic!("the body must contain the outer loop")
		};
		let mir::ExprKind::Sequence { statements } = body.kind(outer_body)
		else {
			panic!("a loop's body is a sequence")
		};
		let mir::ExprKind::Loop {
			label: inner,
			body: inner_body,
		} = body.kind(only(statements))
		else {
			panic!("the outer loop must contain the inner loop")
		};
		let mir::ExprKind::Sequence { statements } = body.kind(inner_body)
		else {
			panic!("a loop's body is a sequence")
		};
		let mir::ExprKind::Continue { label } = body.kind(only(statements))
		else {
			panic!("the inner loop must contain the continue")
		};

		assert_ne!(outer, inner, "each loop needs its own scope");
		assert_eq!(
			label, outer,
			"`continue :outer` must restart the outer loop"
		);
	}
}
