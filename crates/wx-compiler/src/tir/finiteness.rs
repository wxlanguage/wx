//! Finiteness: whether expanding what a type stores directly terminates.
//!
//! Each struct is judged once, its type parameters unknown, and its answer
//! cached; an instance is judged where a projection it stores resolves. A
//! cycle is reported where it closes, from the stack of owners in progress. See "Infinite types" in `notes/pointee-and-sized.md`.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::bounds::AssumptionEnvIdx;
use super::decls::{FieldIdx, StructIdx};
use super::signatures::Semantics;
use super::solver::{NormalizationDepth, RewriteFlags, SolverError};
use super::types::{Substitution, Type, TypeIndex};
use crate::ast::StringInterner;
use crate::diagnostics::{DiagnosticCode, SourceSpan};
use crate::vfs::FileId;

/// A type whose direct contents expand finitely under `env`. Only
/// finiteness constructs one, and every part of one is one, so a walk over
/// fields that starts from one terminates without guarding itself.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct FiniteType {
	env: AssumptionEnvIdx,
	ty: TypeIndex,
}

impl FiniteType {
	pub(super) fn ty(self) -> TypeIndex {
		self.ty
	}

	pub(super) fn env(self) -> AssumptionEnvIdx {
		self.env
	}
}

pub(super) struct Finiteness {
	/// `None` until judged.
	structs: Vec<Option<Expansion>>,
	/// Absent until judged.
	instances: FxHashMap<InstanceKey, Expansion>,
	direct_deps: Vec<TypeIndex>,
	stack: Vec<Step>,
}

/// What expanding an owner's direct contents gives.
#[derive(Clone, Copy)]
enum Expansion {
	Finite { direct_deps: DirectDeps },
	Infinite,
}

/// Where an owner stands relative to the stack.
enum Progress {
	Idle,
	/// In this request's segment: reaching it closes a cycle.
	InRequest {
		at: usize,
	},
	/// Below this request's segment: reached through normalization, a loop
	/// the solver owns (see `Semantics::struct_is_finite`).
	InOuterRequest,
}

/// A struct at its arguments, judged under the facts in `env`: the root
/// environment for a type with nothing abstract in it, as `Normalization`
/// keys it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct InstanceKey {
	env: AssumptionEnvIdx,
	ty: TypeIndex,
}

/// What a finite struct or instance stores directly that depends on the
/// parameters in scope, by kind, as runs of `Finiteness::direct_deps`.
#[derive(Clone, Copy)]
struct DirectDeps {
	/// Parameters stored as they are: `T`. Substituted, the argument itself.
	params: DepRun,
	/// What an impl picks for its parameters: `T::This`. Substituted, it
	/// resolves at an instance or stays a dependency.
	projections: DepRun,
}

#[derive(Clone, Copy)]
struct DepRun {
	start: u32,
	len: u32,
}

/// The dependencies a walk finds, by kind, before they are appended as runs.
#[derive(Default)]
struct FoundDeps {
	params: SmallVec<[TypeIndex; 4]>,
	projections: SmallVec<[TypeIndex; 4]>,
}

/// `owner` holds what its `field` is directly.
#[derive(Clone, Copy)]
struct Step {
	owner: StepOwner,
	field: FieldIdx,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StepOwner {
	/// A struct judged with its type parameters unknown.
	Definition(StructIdx),
	/// A struct at its arguments, judged where a projection dependency
	/// resolves, or found again by a report inside a finished struct.
	Instance(InstanceKey),
}

impl Finiteness {
	pub(super) fn new(struct_count: usize) -> Self {
		Self {
			structs: vec![None; struct_count],
			instances: FxHashMap::default(),
			direct_deps: Vec::new(),
			stack: Vec::new(),
		}
	}

	fn run(&self, run: DepRun) -> &[TypeIndex] {
		&self.direct_deps[run.start as usize..(run.start + run.len) as usize]
	}

	fn push_deps(&mut self, deps: &FoundDeps) -> DirectDeps {
		DirectDeps {
			params: self.push_run(&deps.params),
			projections: self.push_run(&deps.projections),
		}
	}

	/// Appends `deps` as one run, each dependency once.
	fn push_run(&mut self, deps: &[TypeIndex]) -> DepRun {
		let start = self.direct_deps.len();
		for &dep in deps {
			if !self.direct_deps[start..].contains(&dep) {
				self.direct_deps.push(dep);
			}
		}
		DepRun {
			start: u32::try_from(start).unwrap(),
			len: u32::try_from(self.direct_deps.len() - start).unwrap(),
		}
	}

	fn progress(&self, owner: StepOwner, start: usize) -> Progress {
		match self.stack.iter().position(|step| step.owner == owner) {
			None => Progress::Idle,
			Some(at) if at >= start => Progress::InRequest { at },
			Some(_) => Progress::InOuterRequest,
		}
	}

	fn first_instance_since(&self, start: usize) -> Option<usize> {
		(start..self.stack.len())
			.find(|&at| matches!(self.stack[at].owner, StepOwner::Instance(_)))
	}

	fn record(&mut self, owner: StepOwner, expansion: Expansion) {
		match owner {
			StepOwner::Definition(struct_index) => {
				self.structs[usize::from(struct_index)] = Some(expansion);
			}
			StepOwner::Instance(key) => {
				self.instances.insert(key, expansion);
			}
		}
	}
}

impl Semantics {
	/// Whether expanding what `struct_index` stores directly terminates, for
	/// every finite argument. A request asked while another is in progress
	/// (through normalization: a field's `StackValue::Repr` walks fields)
	/// starts its own segment of the stack: a struct in progress below it is
	/// reached through normalization, not stored directly, so that loop is
	/// the solver's and the answer is `Poisoned`. On an error nothing was
	/// recorded, so asking again starts clean.
	pub(super) fn struct_is_finite(
		&mut self,
		strings: &StringInterner,
		struct_index: StructIdx,
	) -> Result<bool, SolverError> {
		let start = self.solver.finiteness.stack.len();
		let finite = self.judge_struct(strings, struct_index, start);
		if finite.is_err() {
			self.solver.finiteness.stack.truncate(start);
		}
		finite.map(|expansion| matches!(expansion, Expansion::Finite { .. }))
	}

	/// `ty` as a finite type under `env`, the root of a walk over fields;
	/// `Poisoned` when infinite, which finiteness reported.
	pub(super) fn finite(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<FiniteType, SolverError> {
		if self.type_is_finite(strings, env, ty)? {
			Ok(FiniteType { env, ty })
		} else {
			Err(SolverError::Poisoned)
		}
	}

	/// `ty` normalized under its own facts, with every rewrite. Finiteness
	/// normalizes without constant values, which change only array lengths
	/// and constants named in types, never what is stored directly, so the
	/// result is finite too.
	pub(super) fn normalize_finite(
		&mut self,
		strings: &StringInterner,
		ty: FiniteType,
		depth: NormalizationDepth,
	) -> Result<FiniteType, SolverError> {
		let normalized =
			self.normalize(strings, ty.env, ty.ty, depth, RewriteFlags::ALL)?;
		Ok(FiniteType {
			env: ty.env,
			ty: normalized,
		})
	}

	/// One expansion step of `ty`: a struct's fields with its arguments
	/// substituted, a tuple's elements, an array's or a slice's element, an
	/// enum's repr; nothing for anything else, a type to normalize first
	/// included.
	pub(super) fn parts(
		&mut self,
		ty: FiniteType,
	) -> SmallVec<[FiniteType; 4]> {
		let part = |part| FiniteType {
			env: ty.env,
			ty: part,
		};
		match *self.types.resolve(ty.ty) {
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let signature = &self.structs[usize::from(struct_index)];
				let (env, fields) =
					(signature.type_params, signature.field_types);
				let args: Box<[TypeIndex]> = self.types.list(type_args).into();
				// Read one field at a time: substituting may store more lists.
				(0..fields.len())
					.map(|at| {
						let field = self.types.list(fields)[at];
						part(self.types.substitute(
							field,
							Substitution {
								envs: &self.generic_envs,
								env,
								args: &args,
							},
						))
					})
					.collect()
			}
			Type::Tuple { elements } => self
				.types
				.list(elements)
				.iter()
				.copied()
				.map(part)
				.collect(),
			Type::Array { of, .. } | Type::Slice { of } => {
				SmallVec::from_elem(part(of), 1)
			}
			Type::Enum { enum_index } => SmallVec::from_elem(
				part(self.enums[usize::from(enum_index)].repr),
				1,
			),
			_ => SmallVec::new(),
		}
	}

	/// Whether expanding what `ty` stores directly terminates under `env`,
	/// a request as `struct_is_finite` is.
	pub(super) fn type_is_finite(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<bool, SolverError> {
		let start = self.solver.finiteness.stack.len();
		let finite = self.walk_direct(
			strings,
			env,
			ty,
			&mut FoundDeps::default(),
			start,
		);
		if finite.is_err() {
			self.solver.finiteness.stack.truncate(start);
		}
		finite
	}

	/// `start` is where the request's segment of the stack begins.
	fn judge_struct(
		&mut self,
		strings: &StringInterner,
		struct_index: StructIdx,
		start: usize,
	) -> Result<Expansion, SolverError> {
		if let Some(expansion) =
			self.solver.finiteness.structs[usize::from(struct_index)]
		{
			return Ok(expansion);
		}
		let env = self.completed_env(
			strings,
			self.structs[usize::from(struct_index)].type_params,
		);
		self.judge(strings, StepOwner::Definition(struct_index), env, start)
	}

	/// Judges an instance whose projection dependency resolves under its
	/// key's facts: its fields, with its arguments substituted.
	fn judge_instance(
		&mut self,
		strings: &StringInterner,
		key: InstanceKey,
		start: usize,
	) -> Result<Expansion, SolverError> {
		if let Some(&expansion) = self.solver.finiteness.instances.get(&key) {
			return Ok(expansion);
		}
		let instances = self.solver.finiteness.stack[start..]
			.iter()
			.filter(|step| matches!(step.owner, StepOwner::Instance(_)))
			.count();
		if instances >= self.solver.recursion_limit {
			let at = self
				.solver
				.finiteness
				.first_instance_since(start)
				.expect("an instance is on the stack");
			self.close_overflow(strings, at);
			return Ok(Expansion::Infinite);
		}
		self.judge(strings, StepOwner::Instance(key), key.env, start)
	}

	/// Judges an owner not judged yet, and records the answer.
	fn judge(
		&mut self,
		strings: &StringInterner,
		owner: StepOwner,
		env: AssumptionEnvIdx,
		start: usize,
	) -> Result<Expansion, SolverError> {
		match self.solver.finiteness.progress(owner, start) {
			Progress::InRequest { at } => {
				self.close_cycle(strings, at);
				return Ok(Expansion::Infinite);
			}
			Progress::InOuterRequest => return Err(SolverError::Poisoned),
			Progress::Idle => {}
		}
		let expansion = self.walk_fields(strings, owner, env, start)?;
		self.solver.finiteness.record(owner, expansion);
		Ok(expansion)
	}

	/// Walks each field of `owner` with a step for it on the stack.
	fn walk_fields(
		&mut self,
		strings: &StringInterner,
		owner: StepOwner,
		env: AssumptionEnvIdx,
		start: usize,
	) -> Result<Expansion, SolverError> {
		let fields = self.structs[usize::from(self.step_struct(owner))]
			.field_types
			.len();
		let mut deps = FoundDeps::default();
		for at in 0..fields {
			let step = Step {
				owner,
				field: FieldIdx::new(u32::try_from(at).unwrap()),
			};
			let field = self.step_field_type(step);
			self.solver.finiteness.stack.push(step);
			let finite =
				self.walk_direct(strings, env, field, &mut deps, start)?;
			self.solver.finiteness.stack.pop();
			if !finite {
				return Ok(Expansion::Infinite);
			}
		}
		let direct_deps = self.solver.finiteness.push_deps(&deps);
		Ok(Expansion::Finite { direct_deps })
	}

	/// Walks what `ty` stores directly under `env`, recording in `deps` what
	/// depends on the parameters in scope. A field that does not normalize is
	/// a leaf: its well-formedness check reports it.
	fn walk_direct(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
		deps: &mut FoundDeps,
		start: usize,
	) -> Result<bool, SolverError> {
		match *self.types.resolve(ty) {
			Type::Tuple { elements } => {
				for at in 0..elements.len() {
					let element = self.types.list(elements)[at];
					if !self.walk_direct(strings, env, element, deps, start)? {
						return Ok(false);
					}
				}
				Ok(true)
			}
			Type::Array { of, .. } | Type::Slice { of } => {
				self.walk_direct(strings, env, of, deps, start)
			}
			Type::TypeParam { .. } => {
				deps.params.push(ty);
				Ok(true)
			}
			Type::TypeProjection { .. } => {
				match self.normalize_for_finiteness(strings, env, ty)? {
					Some(normalized) => {
						self.walk_direct(strings, env, normalized, deps, start)
					}
					None => {
						if self.types.has_param(ty) {
							deps.projections.push(ty);
						}
						Ok(true)
					}
				}
			}
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let Expansion::Finite {
					direct_deps: struct_deps,
				} = self.judge_struct(strings, struct_index, start)?
				else {
					return Ok(false);
				};
				let decl_env =
					self.structs[usize::from(struct_index)].type_params;
				let args: Box<[TypeIndex]> = self.types.list(type_args).into();
				let substitution = |sema: &mut Self, dep| {
					sema.types.substitute(
						dep,
						Substitution {
							envs: &sema.generic_envs,
							env: decl_env,
							args: &args,
						},
					)
				};
				let mut projections = SmallVec::<[TypeIndex; 4]>::new();
				let mut resolves = false;
				for at in 0..struct_deps.projections.len as usize {
					let dep =
						self.solver.finiteness.run(struct_deps.projections)[at];
					let dep = substitution(self, dep);
					resolves |= self
						.normalize_for_finiteness(strings, env, dep)?
						.is_some();
					projections.push(dep);
				}
				if resolves {
					let key = self.instance_key(env, ty);
					let Expansion::Finite {
						direct_deps: instance_deps,
					} = self.judge_instance(strings, key, start)?
					else {
						return Ok(false);
					};
					let finiteness = &self.solver.finiteness;
					deps.params.extend_from_slice(
						finiteness.run(instance_deps.params),
					);
					deps.projections.extend_from_slice(
						finiteness.run(instance_deps.projections),
					);
					return Ok(true);
				}
				for dep in projections {
					if self.types.has_param(dep) {
						deps.projections.push(dep);
					}
				}
				for at in 0..struct_deps.params.len as usize {
					let dep =
						self.solver.finiteness.run(struct_deps.params)[at];
					let dep = substitution(self, dep);
					if !self.walk_direct(strings, env, dep, deps, start)? {
						return Ok(false);
					}
				}
				Ok(true)
			}
			Type::Error
			| Type::Infer
			| Type::Never
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar
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
			| Type::Funcref
			| Type::TypedFuncref { .. }
			| Type::Function { .. }
			| Type::Pointer { .. }
			| Type::Enum { .. }
			| Type::Memory { .. }
			| Type::Global { .. }
			| Type::Value { .. }
			| Type::ConstRef { .. } => Ok(true),
		}
	}

	/// What a projection resolves to under `env`, without constant values
	/// (see "Layout cycles are not infinite types"); `None` when it stays as
	/// it is or does not normalize, which its well-formedness check reports.
	fn normalize_for_finiteness(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<TypeIndex>, SolverError> {
		match self.normalize(
			strings,
			env,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::EQUALITIES | RewriteFlags::DEFINITIONS,
		) {
			Ok(normalized) if normalized != ty => Ok(Some(normalized)),
			Ok(_) => Ok(None),
			Err(SolverError::Pending) => Err(SolverError::Pending),
			Err(_) => Ok(None),
		}
	}

	fn instance_key(
		&self,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> InstanceKey {
		let abstract_parts =
			self.types.has_param(ty) || self.types.has_projection(ty);
		InstanceKey {
			env: if abstract_parts {
				env
			} else {
				AssumptionEnvIdx::ROOT
			},
			ty,
		}
	}

	/// The owners on the stack from `at` up form a cycle: reported from its
	/// first-defined member, and every member is infinite.
	fn close_cycle(&mut self, strings: &StringInterner, at: usize) {
		let mut members = self.solver.finiteness.stack[at..].to_vec();
		let first = (0..members.len())
			.min_by_key(|&member| {
				usize::from(self.step_struct(members[member].owner))
			})
			.expect("a cycle has a member");
		members.rotate_left(first);
		let diagnostic = self.recursive_type_diagnostic(strings, &members);
		self.diagnostics.push(diagnostic);
		for member in members {
			self.solver
				.finiteness
				.record(member.owner, Expansion::Infinite);
		}
	}

	/// The instances on the stack from `at` up grow without repeating, past
	/// the recursion limit: reported from the first, and every owner from it
	/// up is infinite.
	fn close_overflow(&mut self, strings: &StringInterner, at: usize) {
		let members = self.solver.finiteness.stack[at..].to_vec();
		let first = members[0];
		let shown = self.owner_name(strings, first.owner);
		let loc =
			self.decls.structs[usize::from(self.step_struct(first.owner))].loc;
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
			.with_message(format!(
				"expanding `{shown}` exceeded the recursion limit"
			))
			.with_label(self.decls.declaration_span(loc).primary_label())
			.with_note(format!(
				"the recursion limit is {}",
				self.solver.recursion_limit
			));
		for &step in members.iter().take(3) {
			diagnostic = diagnostic
				.with_label(self.stored_directly_label(strings, step));
		}
		self.diagnostics.push(diagnostic);
		for member in members {
			self.solver
				.finiteness
				.record(member.owner, Expansion::Infinite);
		}
	}

	/// Each member with a primary label on its struct and a label on its
	/// field, then the steps inside finished structs that lead from that field
	/// to the next member.
	fn recursive_type_diagnostic(
		&mut self,
		strings: &StringInterner,
		members: &[Step],
	) -> Diagnostic<FileId> {
		let mut names = Vec::with_capacity(members.len());
		let mut labels = Vec::new();
		for (at, &member) in members.iter().enumerate() {
			names.push(self.owner_name(strings, member.owner));
			let loc = self.decls.structs
				[usize::from(self.step_struct(member.owner))]
			.loc;
			labels.push(self.decls.declaration_span(loc).primary_label());
			labels.push(self.stored_directly_label(strings, member));
			let next =
				self.step_struct(members[(at + 1) % members.len()].owner);
			let env = self.owner_env(member.owner);
			let field = self.step_field_type(member);
			let mut hops = Vec::new();
			let found = self.find_direct(strings, env, field, next, &mut hops);
			debug_assert!(found, "a member's field leads to the next member");
			for hop in hops {
				labels.push(self.stored_directly_label(strings, hop));
			}
		}
		let message = match names.as_slice() {
			[only] => format!("recursive type `{only}` has infinite size"),
			[rest @ .., last] => {
				let rest = rest
					.iter()
					.map(|name| format!("`{name}`"))
					.collect::<Vec<_>>()
					.join(", ");
				format!(
					"recursive types {rest} and `{last}` have infinite size"
				)
			}
			[] => unreachable!("a cycle has a member"),
		};
		Diagnostic::error()
			.with_code(DiagnosticCode::RecursiveTypeWithoutIndirection.code())
			.with_message(message)
			.with_labels(labels)
			.with_note("hold one of them through a pointer to break the cycle")
	}

	/// A label on the name of the step's field, saying what it holds
	/// directly.
	fn stored_directly_label(
		&mut self,
		strings: &StringInterner,
		step: Step,
	) -> Label<FileId> {
		let held = self.step_field_type(step);
		let held = self.type_formatter(strings).display_type(held);
		let owner = self.owner_name(strings, step.owner);
		let decl =
			&self.decls.structs[usize::from(self.step_struct(step.owner))];
		let span = SourceSpan::new(
			self.decls.file_id(decl.loc),
			self.decls.fields.name_span(decl.fields, step.field),
		);
		let message = match self.decls.fields.name(decl.fields, step.field) {
			Some(field) => format!(
				"`{held}` in field `{}` of `{owner}` is stored directly",
				strings.resolve(field).expect("a field's name is interned")
			),
			None => {
				format!("`{held}` in a field of `{owner}` is stored directly")
			}
		};
		span.secondary_label().with_message(message)
	}

	/// A definition by its name, an instance as its type.
	fn owner_name(&self, strings: &StringInterner, owner: StepOwner) -> String {
		match owner {
			StepOwner::Definition(struct_index) => strings
				.resolve(
					self.decls
						.item(self.decls.structs[usize::from(struct_index)].loc)
						.name
						.inner,
				)
				.expect("a struct's name is interned")
				.to_owned(),
			StepOwner::Instance(key) => {
				self.type_formatter(strings).display_type(key.ty)
			}
		}
	}

	/// The facts an owner's fields are walked under.
	fn owner_env(&self, owner: StepOwner) -> AssumptionEnvIdx {
		match owner {
			StepOwner::Definition(struct_index) => self
				.assumption_envs
				.completed(self.structs[usize::from(struct_index)].type_params),
			StepOwner::Instance(key) => key.env,
		}
	}

	/// The struct a step's owner is, or is an instance of.
	fn step_struct(&self, owner: StepOwner) -> StructIdx {
		match owner {
			StepOwner::Definition(struct_index) => struct_index,
			StepOwner::Instance(key) => match *self.types.resolve(key.ty) {
				Type::Struct { struct_index, .. } => struct_index,
				_ => unreachable!("an instance owner is a struct"),
			},
		}
	}

	/// The type of the step's field: as written for a definition, with the
	/// instance's arguments substituted for an instance.
	fn step_field_type(&mut self, step: Step) -> TypeIndex {
		let signature =
			&self.structs[usize::from(self.step_struct(step.owner))];
		let (decl_env, fields) = (signature.type_params, signature.field_types);
		let field = self.types.list(fields)[usize::from(step.field)];
		let StepOwner::Instance(key) = step.owner else {
			return field;
		};
		let Type::Struct { type_args, .. } = *self.types.resolve(key.ty) else {
			unreachable!("an instance owner is a struct")
		};
		let args: Box<[TypeIndex]> = self.types.list(type_args).into();
		self.types.substitute(
			field,
			Substitution {
				envs: &self.generic_envs,
				env: decl_env,
				args: &args,
			},
		)
	}

	/// Finds how `ty` stores an instance of `goal` directly, through finished
	/// structs, pushing each step inside one to `hops`. The cold path of a
	/// report: the walk keeps only the members on its stack.
	fn find_direct(
		&mut self,
		strings: &StringInterner,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
		goal: StructIdx,
		hops: &mut Vec<Step>,
	) -> bool {
		if hops.len() >= self.solver.recursion_limit {
			return false;
		}
		match *self.types.resolve(ty) {
			Type::Struct { struct_index, .. } if struct_index == goal => true,
			Type::Struct { struct_index, .. } => {
				if !matches!(
					self.solver.finiteness.structs[usize::from(struct_index)],
					Some(Expansion::Finite { .. })
				) {
					return false;
				}
				let owner = StepOwner::Instance(self.instance_key(env, ty));
				let fields =
					self.structs[usize::from(struct_index)].field_types.len();
				for at in 0..fields {
					let step = Step {
						owner,
						field: FieldIdx::new(u32::try_from(at).unwrap()),
					};
					hops.push(step);
					let held = self.step_field_type(step);
					if self.find_direct(strings, env, held, goal, hops) {
						return true;
					}
					hops.pop();
				}
				false
			}
			Type::Tuple { elements } => (0..elements.len()).any(|at| {
				let element = self.types.list(elements)[at];
				self.find_direct(strings, env, element, goal, hops)
			}),
			Type::Array { of, .. } | Type::Slice { of } => {
				self.find_direct(strings, env, of, goal, hops)
			}
			Type::TypeProjection { .. } => {
				match self.normalize_for_finiteness(strings, env, ty) {
					Ok(Some(normalized)) => {
						self.find_direct(strings, env, normalized, goal, hops)
					}
					_ => false,
				}
			}
			_ => false,
		}
	}
}

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::{Diagnostic, LabelStyle};

	use crate::diagnostics::DiagnosticCode;
	use crate::mir;
	use crate::symbols::Keyword;
	use crate::testing::DiagnosticView;
	use crate::tir::signatures::tests::source_graph;
	use crate::vfs::FileId;

	const PRELUDE: &str = "memory heap: u32;\n";

	fn instantiate(source: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
		let mut strings = Keyword::create_interner();
		let graph = source_graph(source, &mut strings);
		let mut sema = crate::tir::check(&graph, &mut strings);
		let mut mir = crate::tir::lower(&mut sema, &strings)
			.expect("a finite program lowers");
		let module = crate::backend::emit(
			&mut mir,
			&strings,
			Some(mir::inline::Policy::DEFAULT),
		)
		.expect("lowered MIR encodes");
		let engine = wasmtime::Engine::default();
		let module = wasmtime::Module::new(&engine, module.encode())
			.expect("lowered MIR is valid Wasm");
		let mut store = wasmtime::Store::new(&engine, ());
		let instance =
			wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
		(store, instance)
	}

	fn check(source: &str, assert: impl FnOnce(&str, DiagnosticView<'_>)) {
		let source = format!("{PRELUDE}{source}");
		let mut strings = Keyword::create_interner();
		let graph = source_graph(&source, &mut strings);
		let sema = crate::tir::check(&graph, &mut strings);
		assert(
			&source,
			DiagnosticView::new("finiteness", &sema.diagnostics, &graph.files),
		);
	}

	fn assert_codes(source: &str, expected: &[DiagnosticCode]) {
		check(source, |_, diagnostics| diagnostics.assert_codes(expected));
	}

	fn assert_infinite(source: &str) {
		assert_codes(
			source,
			&[DiagnosticCode::RecursiveTypeWithoutIndirection],
		);
	}

	fn assert_finite(source: &str) {
		assert_codes(source, &[]);
	}

	/// The source each label covers, with its message, primary labels marked.
	fn labels(source: &str, diagnostic: &Diagnostic<FileId>) -> Vec<String> {
		diagnostic
			.labels
			.iter()
			.map(|label| {
				let style = match label.style {
					LabelStyle::Primary => "primary",
					LabelStyle::Secondary => "secondary",
				};
				format!(
					"{style} `{}`: {}",
					&source[label.range.clone()],
					label.message
				)
			})
			.collect()
	}

	#[test]
	fn a_struct_storing_itself_through_fields_is_infinite() {
		assert_infinite("struct A(a: A);\nfunc f(a: A) {}");
		assert_infinite("struct A(a: (u32, A));\nfunc f(a: A) {}");
		assert_infinite("struct A(a: (A, A));\nfunc f(a: A) {}");
		assert_infinite("struct A(b: B);\nstruct B(a: A);\nfunc f(a: A) {}");
	}

	#[test]
	fn an_unused_infinite_struct_is_reported_at_its_definition() {
		assert_infinite("struct A(a: A);");
		assert_infinite("struct W<T>(v: T);\nstruct A(w: W<A>);");
		assert_infinite("struct W<T>(v: T);\nstruct S<T>(x: W<S<T>>);");
		assert_infinite("struct A(x: u32, a: [A; 2]);");
	}

	#[test]
	fn a_struct_storing_itself_through_a_type_argument_is_infinite() {
		for source in [
			"struct W<T>(v: T);\nstruct A(w: W<A>);",
			"struct A(w: W<A>);\nstruct W<T>(v: T);",
		] {
			assert_infinite(&format!("{source}\nfunc f(a: A) {{}}"));
		}
	}

	#[test]
	fn a_use_before_the_definition_reports_the_cycle_once() {
		assert_infinite(
			"func f(a: A) {}\nstruct A(w: W<A>);\nstruct W<T>(v: T);",
		);
	}

	#[test]
	fn nesting_does_not_hide_a_type_argument_cycle() {
		for field in ["W<W<A>>", "(u32, W<A>)", "P<u32, A>"] {
			assert_infinite(&format!(
				"struct W<T>(v: T);\nstruct P<T, U>(t: T, u: U);\n\
				 struct A(x: {field});\nfunc f(a: A) {{}}"
			));
		}
	}

	#[test]
	fn a_generic_chain_does_not_hide_a_cycle() {
		assert_infinite(
			"struct W<T>(v: T);\nstruct G<T>(w: W<T>);\nstruct A(g: G<A>);\n\
			 func f(a: A) {}",
		);
	}

	#[test]
	fn a_struct_infinite_by_its_own_definition_is_infinite_for_every_argument()
	{
		assert_infinite(
			"struct W<T>(v: T);\nstruct S<T>(x: W<S<T>>);\nfunc f(s: S<u32>) {}",
		);
		assert_infinite(
			"struct W<T>(v: T);\nstruct S<T>(x: S<W<T>>);\nfunc f(s: S<u32>) {}",
		);
	}

	#[test]
	fn a_mutual_cycle_through_type_arguments_is_reported_once() {
		assert_infinite(
			"struct W<T>(v: T);\nstruct B(w: W<C>);\nstruct C(w: W<B>);\n\
			 func f(b: B, c: C) {}",
		);
	}

	#[test]
	fn a_struct_reaching_itself_through_two_fields_is_reported_once() {
		assert_infinite(
			"struct A(b: B, c: C);\nstruct B(a: A);\nstruct C(a: A);",
		);
	}

	#[test]
	fn a_constant_of_an_infinite_struct_is_reported_only_on_the_struct() {
		assert_infinite(
			"struct W<T>(v: T);\nstruct A(w: W<A>);\nconst C: A = A(W(C));",
		);
	}

	#[test]
	fn a_struct_holding_a_cycle_is_not_reported_again() {
		assert_infinite(
			"struct W<T>(v: T);\nstruct A(w: W<A>);\nstruct Outer(a: A);\n\
			 func f(o: Outer) {}",
		);
	}

	#[test]
	fn an_alias_does_not_hide_a_cycle() {
		assert_infinite(
			"struct W<T>(v: T);\ntype WA = W<A>;\nstruct A(w: WA);\nfunc f(a: A) {}",
		);
		for source in [
			"type Store = State;\nstruct Handler(s: Store);\nstruct State(h: Handler);",
			"struct State(h: Handler);\nstruct Handler(s: Store);\ntype Store = State;",
			"struct Handler(s: Store);\ntype Store = State;\nstruct State(h: Handler);",
		] {
			assert_infinite(source);
		}
	}

	#[test]
	fn an_array_element_is_stored_directly_whatever_its_length() {
		for length in [2, 0] {
			assert_infinite(&format!(
				"struct A(x: u32, a: [A; {length}]);\n\
				 func f(p: heap::*A) -> u32 {{ p.x }}"
			));
		}
	}

	#[test]
	fn a_slice_element_is_stored_directly() {
		assert_infinite(
			"struct A(x: u32, tail: [A]);\nfunc f(p: heap::*A) -> u32 { p.x }",
		);
	}

	#[test]
	fn a_projection_resolved_in_the_definition_is_followed() {
		let id = "trait Id { type This; }\n";
		assert_infinite(&format!(
			"{id}impl Id for u32 {{ type This = A; }}\n\
			 struct A(x: <u32 as Id>::This);"
		));
		assert_finite(&format!(
			"{id}impl Id for u32 {{ type This = u8; }}\n\
			 struct A(x: <u32 as Id>::This);\nfunc f(a: A) {{}}"
		));
	}

	/// Normalizing `Repr` walks fields, which normalize the same `Repr`: the
	/// solver owns that loop. `B` holds `A` directly but `A` does not hold
	/// `B`, so a cycle through both is not one of direct storage.
	#[test]
	fn a_loop_through_stack_value_repr_is_the_solvers() {
		for source in [
			"struct A(x: u32, y: <A as StackValue>::Repr);\nfunc f(a: A) {}",
			"struct A(y: <B as StackValue>::Repr);\nstruct B(a: A);",
			"struct B(a: A);\nstruct A(y: <B as StackValue>::Repr);",
		] {
			assert_codes(source, &[DiagnosticCode::CyclicAssociatedType]);
		}
	}

	#[test]
	fn a_wrong_argument_count_reports_only_the_count() {
		for field in ["W", "W<A, A>"] {
			assert_codes(
				&format!("struct W<T>(v: T);\nstruct A(w: {field});"),
				&[DiagnosticCode::TypeArgumentCountMismatch],
			);
		}
	}

	#[test]
	fn the_report_names_each_step_of_the_chain() {
		check(
			"struct W<T>(v: T);\nstruct A(w: W<A>);",
			|source, diagnostics| {
				diagnostics.assert_error_with(
					DiagnosticCode::RecursiveTypeWithoutIndirection,
					|diagnostic| {
						assert_eq!(
							diagnostic.message,
							"recursive type `A` has infinite size"
						);
						assert_eq!(
							labels(source, diagnostic),
							[
								"primary `A`: ",
								"secondary `w`: `W<A>` in field `w` of `A` is stored directly",
								"secondary `v`: `A` in field `v` of `W<A>` is stored directly",
							]
						);
						assert_eq!(
							diagnostic.notes,
							[
								"hold one of them through a pointer to break the cycle"
							]
						);
					},
				);
			},
		);
	}

	#[test]
	fn a_mutual_cycle_is_reported_from_its_first_defined_member() {
		check(
			"func f(c: C) {}\nstruct B(c: C);\nstruct C(b: B);",
			|source, diagnostics| {
				diagnostics.assert_error_with(
					DiagnosticCode::RecursiveTypeWithoutIndirection,
					|diagnostic| {
						assert_eq!(
							diagnostic.message,
							"recursive types `B` and `C` have infinite size"
						);
						assert_eq!(
							labels(source, diagnostic),
							[
								"primary `B`: ",
								"secondary `c`: `C` in field `c` of `B` is stored directly",
								"primary `C`: ",
								"secondary `b`: `B` in field `b` of `C` is stored directly",
							]
						);
					},
				);
			},
		);
	}

	#[test]
	fn a_pointer_stops_the_walk() {
		assert_finite(
			"struct W<T>(v: T);\nstruct A(x: u32, w: W<heap::*A>);\n\
			 func f(a: A) -> u32 { a.x }",
		);
		for source in [
			"struct Handler(s: heap::*State);\nstruct State(x: u32, h: Handler);",
			"struct State(x: u32, h: Handler);\nstruct Handler(s: heap::*State);",
			"type Store = heap::*State;\nstruct Handler(s: Store);\n\
			 struct State(x: u32, h: Handler);",
			"struct State(x: u32, h: Handler);\nstruct Handler(s: Store);\n\
			 type Store = heap::*State;",
		] {
			assert_finite(&format!(
				"{source}\nfunc f(s: State) -> u32 {{ s.x }}"
			));
		}
	}

	#[test]
	fn an_argument_that_does_not_embed_the_struct_is_finite() {
		assert_finite(
			"struct W<T>(v: T);\nstruct G<T>(w: W<T>);\nstruct A(g: G<u32>);\n\
			 func f(a: A) -> u32 { a.g.w.v }",
		);
	}

	#[test]
	fn an_enum_is_stored_directly_as_its_repr() {
		assert_finite(
			"enum E(value: u32) { X = 1 }\nstruct A(e: E, next: heap::*A);\n\
			 func f(a: A) -> E { a.e }",
		);
	}

	#[test]
	fn a_finite_generic_struct_is_finite_in_generic_code() {
		assert_finite(
			"struct W<T>(v: T);\nstruct P<T>(w: W<T>, t: T);\n\
			 func get<T: StackValue>(p: P<T>) -> T { p.w.v }\n\
			 func wrap<T: StackValue>(t: T) -> P<W<T>> { P(W(W(t)), W(t)) }",
		);
	}

	#[test]
	fn finite_structs_around_cycles_build_and_run() {
		let source = r#"
			memory heap: u32;
			struct W<T>(v: T);
			struct G<T>(w: W<T>);
			struct P<T>(w: W<T>, t: T);
			struct Node(value: u32, next: W<heap::*Node>);
			struct Handler(s: heap::*State);
			struct State(value: u32, h: Handler);
			struct Holder(g: G<u32>);
			func node(value: u32) -> u32 {
				Node(value, W(transmute((0: u32)))).value
			}
			func state(value: u32) -> u32 {
				State(value, Handler(transmute((0: u32)))).value
			}
			func holder(value: u32) -> u32 {
				Holder(G(W(value))).g.w.v
			}
			func get<T: StackValue>(p: P<T>) -> T { p.w.v }
			func wrap<T: StackValue>(t: T) -> P<W<T>> { P(W(W(t)), W(t)) }
			func generic(value: u32) -> u32 {
				get(wrap(value)).v
			}
			export {
				node as "node",
				state as "state",
				holder as "holder",
				generic as "generic",
			}
		"#;
		let (mut store, instance) = instantiate(source);
		for name in ["node", "state", "holder", "generic"] {
			let run = instance
				.get_typed_func::<u32, u32>(&mut store, name)
				.unwrap();
			assert_eq!(run.call(&mut store, 7).unwrap(), 7, "{name}");
		}
	}
	const ID: &str = "trait Id { type This; }\nstruct S<T: Id>(x: T::This);\n";
	const LEVEL: &str = "trait Level { type Child; }\n\
		struct Table<L: Level>(entries: [L::Child; 4]);\n\
		impl Level for u16 { type Child = u32; }\n";

	#[test]
	fn a_projection_cycle_through_an_impl_is_infinite_at_its_instance() {
		assert_infinite(&format!(
			"{ID}impl Id for u32 {{ type This = S<u32>; }}\nfunc f(s: S<u32>) {{}}"
		));
	}

	#[test]
	fn an_unused_projection_cycle_is_reported_at_the_impl() {
		assert_infinite(&format!(
			"{ID}impl Id for u32 {{ type This = S<u32>; }}"
		));
	}

	#[test]
	fn a_generic_impl_repeating_its_instance_is_infinite() {
		assert_infinite(&format!(
			"{ID}struct W<T>(v: T);\nimpl<T> Id for W<T> {{ type This = S<W<T>>; }}"
		));
	}

	#[test]
	fn a_generic_impl_growing_its_instance_exceeds_the_limit() {
		check(
			&format!(
				"{ID}struct W<T>(v: T);\nimpl Id for u8 {{ type This = u8; }}\n\
				 impl<T: Id> Id for W<T> {{ type This = S<W<W<T>>>; }}\n\
				 func f(s: S<W<u8>>) {{}}"
			),
			|_, diagnostics| {
				diagnostics.assert_codes(&[
					DiagnosticCode::RecursiveTypeWithoutIndirection,
				]);
				diagnostics.assert_error_saying("exceeded the recursion limit");
			},
		);
	}

	/// The impl's member owns the failure: a concrete instance derived from it
	/// reads a failed member and stays silent, whichever comes first.
	#[test]
	fn an_instance_derived_from_an_infinite_impl_value_is_not_reported_again() {
		for value in ["S<W<T>>", "S<W<W<T>>>"] {
			assert_infinite(&format!(
				"{ID}struct W<T>(v: T);\nimpl Id for u32 {{ type This = u32; }}\n\
				 func f(s: S<W<u32>>) {{}}\n\
				 impl<T: Id> Id for W<T> {{ type This = {value}; }}"
			));
		}
	}

	#[test]
	fn instances_of_one_struct_at_different_arguments_are_finite() {
		assert_finite(&format!(
			"{ID}impl Id for u32 {{ type This = S<u8>; }}\n\
			 impl Id for u8 {{ type This = u32; }}\n\
			 func f(s: S<u32>) -> u32 {{ s.x.x }}"
		));
	}

	#[test]
	fn recursion_through_different_impl_members_is_finite() {
		assert_finite(&format!(
			"{LEVEL}impl Level for u32 {{ type Child = Table<u16>; }}\n\
			 func f(p: heap::*Table<u32>) -> u32 {{ p.entries[0].entries[1] }}"
		));
	}

	#[test]
	fn recursion_that_shrinks_is_finite() {
		assert_finite(&format!(
			"{LEVEL}struct W<T>(v: T);\n\
			 impl<T: Level> Level for W<T> {{ type Child = Table<T>; }}\n\
			 func f(p: heap::*Table<W<W<u16>>>) -> u32 {{\n\
			 	p.entries[0].entries[1].entries[2]\n\
			 }}"
		));
	}

	/// A rule requiring an impl member to be reached again only at smaller
	/// arguments would reject this, while accepting `S<W<W<u16>>>`, which
	/// `S<W<u8>>` holds.
	#[test]
	fn a_finite_instance_reached_through_a_larger_argument_is_finite() {
		assert_finite(&format!(
			"{ID}struct W<T>(v: T);\n\
			 impl<T: Id> Id for W<T> {{ type This = S<T>; }}\n\
			 impl Id for u8 {{ type This = S<W<W<u16>>>; }}\n\
			 impl Id for u16 {{ type This = u32; }}\n\
			 func f(s: S<W<u8>>) {{}}"
		));
	}

	#[test]
	fn finite_projection_instances_build_and_run() {
		let source = format!(
			"#[memory_limits{{ min_pages: 1 }}]\nmemory heap: u32;\n\
			 {ID}{LEVEL}impl Id for u32 {{ type This = S<u8>; }}\n\
			 impl Id for u8 {{ type This = u32; }}\n\
			 impl Level for u32 {{ type Child = Table<u16>; }}\n\
			 func instance(value: u32) -> u32 {{\n\
			 	local s: S<u32> = S(S(value));\n\
			 	s.x.x\n\
			 }}\n\
			 func table(at: u32) -> u32 {{\n\
			 	local p: heap::*Table<u32> = transmute(at);\n\
			 	p.entries[1].entries[2]\n\
			 }}\n\
			 export {{ instance as \"instance\", table as \"table\" }}"
		);
		let (mut store, instance) = instantiate(&source);
		for (name, argument, expected) in [("instance", 7, 7), ("table", 0, 0)]
		{
			let run = instance
				.get_typed_func::<u32, u32>(&mut store, name)
				.unwrap();
			assert_eq!(
				run.call(&mut store, argument).unwrap(),
				expected,
				"{name}"
			);
		}
	}
}
