//! TIR pattern lowering.
//!
//! A match evaluates its scrutinee once and then tries its arms in order. The
//! checked pattern arena can describe structure (`Tuple`, `Struct`), tests
//! (`Int`, `Char`, `Constant`) and alternatives (`Or`). MIR `Switch` only
//! describes a scalar selector with one discriminant per arm, so scalar-only
//! matches lower there — `opt` can then choose between `br_table` and a
//! compare chain. Everything else lowers to an ordered `IfElse` decision
//! tree: each arm's pattern becomes a boolean condition over projections of
//! the stored scrutinee, and its bindings run only on the branch that matched.
//!
//! Pattern tests and projections read the stored scrutinee and are assumed to
//! have no side effects (an aggregate test calls the type's `Eq`), so an `Or`
//! binding selector may re-test alternatives to find out which one bound the
//! names. Only the arm body is lowered once.
//!
//! A `local` pattern is irrefutable, so it has no tests or decision tree. It
//! uses the same projections and binding stores, with its initializer
//! evaluated once into the projection root first.

use std::collections::HashSet;

use super::{
	Body, ExprIdx, FunctionState, LocalRun, Lowerer, ScalarRange, mir,
};
use crate::ast::BinaryOp;
use crate::diagnostics::TextSpan;
use crate::tir::body::{
	Arm, ArmRange, ExprKind, PatIdx, PatternKind, PatternRange,
};
use crate::tir::bounds::AssumptionEnvIdx;
use crate::tir::decls::{ConstIdx, FieldIdx, MemberKind};
use crate::tir::members::{TraitImplLookup, TraitMemberSelection};
use crate::tir::types::Primitive;
use crate::tir::types::{GenericArgs, Type, TypeIndex};

/// A value of the match scrutinee at some field path, read from one root
/// local. `range` is a flat scalar range in that local and `tir_ty` says what
/// the range means (so nested projections can be computed without keeping a
/// separate type stack).
#[derive(Clone, Copy)]
struct Projection {
	/// The locals of the stored value the projection is rooted in.
	root: LocalRun,
	range: ScalarRange,
	ty: mir::ValueType,
	/// Concrete: substituted with the instance's arguments where it was read.
	tir_ty: TypeIndex,
}

impl Lowerer<'_> {
	/// Lower `local pattern = value`. The initializer runs exactly once,
	/// before any binding. A binding or wildcard keeps the direct store/drop
	/// form; anything structural is read through a projection of that one
	/// value, spilling a non-local initializer into a temporary first.
	///
	/// A local pattern is irrefutable, so it needs no test; the same
	/// structural reads that bind a match arm's names apply here.
	pub(super) fn lower_local_declaration(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		value: ExprIdx,
		pattern: PatIdx,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		// A diverging initializer means no binding runs; keep its `Never`.
		if ty == mir::ValueType::Never {
			let value = self.lower_expr(body, state, value)?;
			#[cfg(debug_assertions)]
			debug_assert_eq!(state.ty(value), mir::ValueType::Never);
			return Ok(value);
		}
		match body.pattern(pattern) {
			PatternKind::Wildcard => {
				let value = self.lower_expr(body, state, value)?;
				return Ok(state.push(
					mir::ExprKind::Drop { value },
					mir::ValueType::Unit,
				));
			}
			PatternKind::Bind(local) => {
				let value = self.lower_expr(body, state, value)?;
				let run = state.local_map[usize::from(local)];
				return Ok(self.write_locals(state, run, value));
			}
			_ => {}
		}

		debug_assert!(
			self.pattern_irrefutable(body, pattern),
			"a local pattern always matches"
		);
		let value_ty = self.expr_ty(body, state, value);
		let value_ty =
			self.lower_type(value_ty, state.file_id, body.span(value))?;
		let (subject, prefix) =
			self.lower_subject(body, state, value, value_ty)?;
		let mut bindings = Vec::new();
		self.collect_bindings(body, state, pattern, subject, &mut bindings)?;
		let result = self.bindings_value(state, bindings);
		Ok(self.sequence(state, prefix, result))
	}

	/// Lower `match scrutinee { arms }`, whose checked type is `ty`.
	pub(super) fn lower_match(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		scrutinee: ExprIdx,
		arms: ArmRange,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let tir_ty = self.expr_ty(body, state, scrutinee);
		let scrutinee_ty =
			self.lower_type(tir_ty, state.file_id, body.span(scrutinee))?;
		// A struct of one scalar is that scalar, but a constant of its type
		// compares by the type's `PartialEq`, which a `Switch` cannot ask.
		let tir_ty =
			self.normalize_type(tir_ty, state.file_id, body.span(scrutinee))?;
		let compares_by_eq = matches!(
			self.sema.types.resolve(tir_ty),
			Type::Struct { .. } | Type::Tuple { .. }
		);
		// A diverging scrutinee means no arm runs. Keeping the scrutinee's
		// `Never` value makes the match diverge too; the arms' checked result
		// types are irrelevant on that path.
		if scrutinee_ty == mir::ValueType::Never {
			let value = self.lower_expr(body, state, scrutinee)?;
			#[cfg(debug_assertions)]
			debug_assert_eq!(state.ty(value), mir::ValueType::Never);
			return Ok(value);
		}

		let arms = body.arms(arms);
		// Once an arm's pattern always matches, later arms are unreachable.
		// The checker warns about them, but they must not win at runtime.
		let effective = arms
			.iter()
			.position(|arm| self.pattern_irrefutable(body, arm.pattern))
			.map_or(arms.len(), |at| at + 1);
		let arms = &arms[..effective];

		let primitive =
			self.scalar_primitive(tir_ty, state.file_id, body.span(scrutinee))?;
		if !compares_by_eq
			&& let Some(discriminants) =
				self.switch_discriminants(body, arms, scrutinee_ty, primitive)
		{
			return self.lower_switch_match(
				body,
				state,
				scrutinee,
				arms,
				&discriminants,
				scrutinee_ty,
				ty,
			);
		}
		self.lower_tree_match(body, state, scrutinee, arms, scrutinee_ty, ty)
	}

	/// Whether `pattern` matches every value of its type without a test.
	fn pattern_irrefutable(&self, body: &Body, pattern: PatIdx) -> bool {
		match body.pattern(pattern) {
			PatternKind::Wildcard | PatternKind::Bind(_) => true,
			PatternKind::Tuple(children) => body
				.patterns(children)
				.iter()
				.all(|&child| self.pattern_irrefutable(body, child)),
			PatternKind::Struct { fields, .. } => {
				self.pattern_irrefutable(body, fields)
			}
			PatternKind::Or(alternatives) => {
				body.patterns(alternatives).iter().any(|&alternative| {
					self.pattern_irrefutable(body, alternative)
				})
			}
			PatternKind::Int(_)
			| PatternKind::Char(_)
			| PatternKind::Constant { .. }
			| PatternKind::AbstractConstant { .. }
			| PatternKind::Error => false,
		}
	}

	/// The discriminants a scalar-only match can put in a MIR `Switch`, in
	/// arm order. `None` is an irrefutable arm (the default). `None` for the
	/// whole result means the match needs the general decision tree.
	fn switch_discriminants(
		&mut self,
		body: &Body,
		arms: &[Arm],
		ty: mir::ValueType,
		primitive: Option<Primitive>,
	) -> Option<Vec<Option<i64>>> {
		// `Switch` compares integer discriminants. Floats have no canonical
		// integer selector here, so they take the decision tree instead.
		if !ty.is_integer() {
			return None;
		}
		let mut discriminants = Vec::with_capacity(arms.len());
		for arm in arms {
			let discriminant = match body.pattern(arm.pattern) {
				PatternKind::Int(bits) => {
					Some(pattern_int_discriminant(bits, primitive?)?)
				}
				PatternKind::Constant {
					constant,
					type_args,
				} => {
					if !type_args.is_empty() {
						return None;
					}
					match self.sema.constant_bits(self.strings, constant) {
						Ok(Some(bits)) => {
							Some(constant_int_discriminant(bits, ty)?)
						}
						Ok(None) | Err(_) => return None,
					}
				}
				PatternKind::Wildcard | PatternKind::Bind(_) => None,
				_ => return None,
			};
			discriminants.push(discriminant);
		}
		Some(discriminants)
	}

	/// Lower a match whose arms are scalar tests (plus, at most, one trailing
	/// wildcard or binding). The scrutinee is evaluated once; a binding
	/// default needs its value after the selector was already read, so that
	/// case stores the scrutinee in a temporary first.
	fn lower_switch_match(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		scrutinee: ExprIdx,
		arms: &[Arm],
		discriminants: &[Option<i64>],
		scrutinee_ty: mir::ValueType,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let default_binding = match arms.last() {
			Some(arm) => match body.pattern(arm.pattern) {
				PatternKind::Wildcard => Some(None),
				PatternKind::Bind(local) => Some(Some(local)),
				_ => None,
			},
			None => None,
		};
		let binds_default = matches!(default_binding, Some(Some(_)));

		let mut prefix = Vec::new();
		let (selector, subject) = if binds_default {
			let (subject, spill) =
				self.lower_subject(body, state, scrutinee, scrutinee_ty)?;
			prefix = spill;
			(self.projection_value(state, subject), Some(subject))
		} else {
			(self.lower_expr(body, state, scrutinee)?, None)
		};

		let mut seen = HashSet::new();
		let mut cases = Vec::new();
		let mut default = None;
		for (arm, discriminant) in arms.iter().zip(discriminants) {
			match discriminant {
				Some(discriminant) => {
					// A duplicate test is unreachable: the first arm wins.
					// Dropping later duplicates is also required by the
					// `br_table` path, which maps one depth per value.
					if !seen.insert(*discriminant) {
						continue;
					}
					let body = self.lower_expr(body, state, arm.body)?;
					cases.push(mir::Case {
						value: *discriminant,
						body,
					});
				}
				None => default = Some(arm),
			}
		}

		let default = match default {
			Some(arm) => {
				let value = self.lower_expr(body, state, arm.body)?;
				let value = match default_binding {
					Some(Some(local)) => {
						let subject = subject
							.expect("a binding default has a stored scrutinee");
						let bind = self.projection_value(state, subject);
						let run = state.local_map[usize::from(local)];
						let set = self.write_locals(state, run, bind);
						self.sequence(state, vec![set], value)
					}
					_ => value,
				};
				Some(value)
			}
			None => None,
		};

		let cases = state.mir_body.push_cases(cases);
		let switch = state.push(
			mir::ExprKind::Switch {
				selector,
				cases,
				default,
			},
			ty,
		);
		Ok(self.sequence(state, prefix, switch))
	}

	/// Lower a match to an ordered `IfElse` tree. The scrutinee is stored in
	/// a local first because tests and bindings may read several of its
	/// fields.
	fn lower_tree_match(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		scrutinee: ExprIdx,
		arms: &[Arm],
		scrutinee_ty: mir::ValueType,
		ty: mir::ValueType,
	) -> Result<mir::ExprId, ()> {
		let (subject, prefix) =
			self.lower_subject(body, state, scrutinee, scrutinee_ty)?;
		// What runs when no arm matched so far: nothing yet. A trailing
		// refutable arm makes it an `unreachable`, built only then, so no node
		// is left out of the tree.
		let mut result: Option<mir::ExprId> = None;
		// Built from the last arm back, so no recursion depth depends on the
		// number of arms.
		for arm in arms.iter().rev() {
			let condition = self.lower_pattern_condition(
				body,
				state,
				arm.pattern,
				subject,
			)?;
			let mut bindings = Vec::new();
			self.collect_bindings(
				body,
				state,
				arm.pattern,
				subject,
				&mut bindings,
			)?;
			let value = self.lower_expr(body, state, arm.body)?;
			let value = self.sequence(state, bindings, value);
			result = Some(match (condition, result) {
				// An irrefutable arm's body is the tree's base; earlier
				// arms still wrap it.
				(None, None) => value,
				(condition, otherwise) => {
					let condition =
						condition.unwrap_or_else(|| state.boolean(true));
					let otherwise = otherwise.unwrap_or_else(|| {
						state.push(
							mir::ExprKind::Unreachable,
							mir::ValueType::Never,
						)
					});
					state.push(
						mir::ExprKind::IfElse {
							condition,
							then: value,
							otherwise: Some(otherwise),
						},
						ty,
					)
				}
			});
		}
		let result = result.unwrap_or_else(|| {
			state.push(mir::ExprKind::Unreachable, mir::ValueType::Never)
		});
		Ok(self.sequence(state, prefix, result))
	}

	/// The scrutinee as a projection rooted in a local. A non-local
	/// expression is evaluated once into a temporary and any resulting setup
	/// is returned as a prefix.
	fn lower_subject(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		scrutinee: ExprIdx,
		ty: mir::ValueType,
	) -> Result<(Projection, Vec<mir::ExprId>), ()> {
		let tir_ty = self.expr_ty(body, state, scrutinee);
		let (root, prefix) = match body.kind(scrutinee) {
			ExprKind::Local(local) => {
				(state.local_map[usize::from(local)], Vec::new())
			}
			_ => {
				let value = self.lower_expr(body, state, scrutinee)?;
				#[cfg(debug_assertions)]
				debug_assert_eq!(state.ty(value), ty);
				let (set, root) = self.temporary(state, value);
				(root, vec![set])
			}
		};
		let len = self.signatures.scalars(&ty).len() as u32;
		Ok((
			Projection {
				root,
				range: ScalarRange::new(0, len),
				ty,
				tir_ty,
			},
			prefix,
		))
	}

	/// A pattern's test, or `None` when it always matches. Conditions compare
	/// projections of the stored scrutinee; no arm body runs here.
	fn lower_pattern_condition(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		pattern: PatIdx,
		subject: Projection,
	) -> Result<Option<mir::ExprId>, ()> {
		match body.pattern(pattern) {
			PatternKind::Wildcard | PatternKind::Bind(_) => Ok(None),
			PatternKind::Tuple(children) => {
				let mut condition = None;
				for (at, &child) in body.patterns(children).iter().enumerate() {
					let child_ty = self.pattern_ty(body, state, child);
					let span = body.pattern_span(child);
					let child_subject = self.project_field(
						state,
						subject,
						FieldIdx::new(at as u32),
						child_ty,
						span,
					)?;
					let child_condition = self.lower_pattern_condition(
						body,
						state,
						child,
						child_subject,
					)?;
					condition =
						and_conditions(state, condition, child_condition);
				}
				Ok(condition)
			}
			PatternKind::Struct { fields, .. } => {
				let fields_ty = self.pattern_ty(body, state, fields);
				let subject = self.retype(
					state,
					subject,
					fields_ty,
					body.pattern_span(fields),
				)?;
				self.lower_pattern_condition(body, state, fields, subject)
			}
			PatternKind::Int(bits) => {
				let primitive = self.scalar_primitive(
					subject.tir_ty,
					state.file_id,
					body.pattern_span(pattern),
				)?;
				let Some(discriminant) = primitive.and_then(|primitive| {
					pattern_int_discriminant(bits, primitive)
				}) else {
					self.unsupported(
						state.file_id,
						body.pattern_span(pattern),
						"an integer pattern of a non-integer type",
					)?;
					unreachable!()
				};
				Ok(Some(self.scalar_test(state, subject, discriminant)))
			}
			PatternKind::Char(value) => {
				let span = body.pattern_span(pattern);
				let field_types = self.aggregate_field_types(
					subject.tir_ty,
					state.file_id,
					span,
				)?;
				let [field_ty] = field_types.as_slice() else {
					self.unsupported(
						state.file_id,
						span,
						"a character pattern on a type that is not one codepoint",
					)?;
					unreachable!()
				};
				let field = self.project_field(
					state,
					subject,
					FieldIdx::new(0),
					*field_ty,
					span,
				)?;
				let primitive =
					self.scalar_primitive(field.tir_ty, state.file_id, span)?;
				let Some(codepoint) = primitive.and_then(|primitive| {
					pattern_int_discriminant(u64::from(value), primitive)
				}) else {
					self.unsupported(
						state.file_id,
						span,
						"a character pattern on a non-integer field",
					)?;
					unreachable!()
				};
				Ok(Some(self.scalar_test(state, field, codepoint)))
			}
			PatternKind::Constant {
				constant,
				type_args,
			} => self.lower_constant_pattern(
				body, state, pattern, subject, constant, type_args,
			),
			PatternKind::AbstractConstant { .. } => {
				self.unsupported(
					state.file_id,
					body.pattern_span(pattern),
					"an abstract constant pattern (trait dispatch is not implemented)",
				)?;
				unreachable!()
			}
			PatternKind::Or(alternatives) => {
				let alternatives = body.patterns(alternatives);
				if alternatives.is_empty() {
					self.unsupported(
						state.file_id,
						body.pattern_span(pattern),
						"an empty `|` pattern",
					)?;
					unreachable!()
				}
				// One alternative always matches, so the whole arm does.
				// Earlier alternatives still matter to the binding selector,
				// but not to this condition, which is then never built.
				if alternatives.iter().any(|&alternative| {
					self.pattern_irrefutable(body, alternative)
				}) {
					return Ok(None);
				}
				let mut condition = None;
				for &alternative in alternatives {
					// A test that turns out to always hold is `true`, so the
					// alternatives already built stay in the tree.
					let next = match self.lower_pattern_condition(
						body,
						state,
						alternative,
						subject,
					)? {
						Some(next) => next,
						None => state.boolean(true),
					};
					condition = or_conditions(state, condition, Some(next));
				}
				Ok(condition)
			}
			PatternKind::Error => {
				self.unsupported(
					state.file_id,
					body.pattern_span(pattern),
					"an erroneous pattern",
				)?;
				unreachable!()
			}
		}
	}

	/// A constant pattern. A scalar compares natively; an aggregate value
	/// compares through the `PartialEq` impl its checked `Eq` bound selects,
	/// so the type's own equality is honoured.
	fn lower_constant_pattern(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		pattern: PatIdx,
		subject: Projection,
		constant: ConstIdx,
		type_args: GenericArgs,
	) -> Result<Option<mir::ExprId>, ()> {
		let span = body.pattern_span(pattern);
		if !type_args.is_empty() {
			self.unsupported(
				state.file_id,
				span,
				"an associated or generic constant pattern",
			)?;
			unreachable!()
		}
		let value = match self.sema.const_value(self.strings, constant) {
			Ok(value) => value.to_vec(),
			Err(_) => {
				self.unsupported(
					state.file_id,
					span,
					"a constant pattern with no value",
				)?;
				unreachable!()
			}
		};
		if subject.ty == mir::ValueType::Unit {
			if value.is_empty() {
				return Ok(None);
			}
			self.unsupported(
				state.file_id,
				span,
				"a constant pattern whose value does not match its type",
			)?;
			unreachable!()
		}
		// A struct or a tuple compares by its type's `PartialEq`, however
		// many scalars it is: `P(x: i32)`'s may compare less than `x`.
		if matches!(
			self.sema.types.resolve(subject.tir_ty),
			Type::Struct { .. } | Type::Tuple { .. }
		) {
			let file_id = state.file_id;
			let value = self.materialize_constant(
				state, file_id, span, subject.ty, &value,
			)?;
			return Ok(Some(self.equality_test(state, subject, value, span)?));
		}
		if matches!(subject.ty, mir::ValueType::F32 | mir::ValueType::F64) {
			self.unsupported(
				state.file_id,
				span,
				"a float constant pattern (floats have no total equality)",
			)?;
			unreachable!()
		}
		let [scalar] = value.as_slice() else {
			self.unsupported(
				state.file_id,
				span,
				"a scalar constant pattern with several values",
			)?;
			unreachable!()
		};
		let file_id = state.file_id;
		let constant =
			self.constant_scalar(state, file_id, span, subject.ty, *scalar)?;
		let left = self.projection_value(state, subject);
		Ok(Some(state.push(
			mir::ExprKind::Compare {
				op: mir::CompareOp::Eq,
				lhs: left,
				rhs: constant,
			},
			mir::ValueType::I32,
		)))
	}

	/// `subject == value` through the concrete `PartialEq::eq` impl that the
	/// pattern's checked `Eq` bound requires. An aggregate's equality is its
	/// impl's, not a field-by-field comparison, so a type may define equality
	/// that differs from its representation.
	fn equality_test(
		&mut self,
		state: &mut FunctionState,
		subject: Projection,
		value: mir::ExprId,
		span: TextSpan,
	) -> Result<mir::ExprId, ()> {
		let Some(method) = self.sema.operators.binary(BinaryOp::Eq) else {
			self.unsupported(
				state.file_id,
				span,
				"an aggregate pattern without the `PartialEq` operator",
			)?;
			unreachable!()
		};
		// The subject's type is concrete, so no assumption can apply.
		let lookup = match self.sema.find_trait_impl_query(
			self.strings,
			AssumptionEnvIdx::ROOT,
			subject.tir_ty,
			method.trait_index,
		) {
			Ok(Some(lookup)) => lookup,
			Ok(None) => {
				self.unsupported(
					state.file_id,
					span,
					"an aggregate pattern whose type implements no `PartialEq`",
				)?;
				unreachable!()
			}
			Err(_) => {
				self.unsupported(
					state.file_id,
					span,
					"an aggregate pattern whose equality impl cannot be resolved",
				)?;
				unreachable!()
			}
		};
		let TraitImplLookup::Concrete { impl_index, args } = lookup else {
			self.unsupported(
				state.file_id,
				span,
				"an aggregate pattern without a concrete equality impl",
			)?;
			unreachable!()
		};
		let TraitMemberSelection::Impl(
			MemberKind::Method(function) | MemberKind::Function(function),
		) = self
			.sema
			.decls
			.select_trait_member(impl_index, MemberKind::Method(method.method))
		else {
			self.unsupported(
				state.file_id,
				span,
				"an equality method that the impl does not provide",
			)?;
			unreachable!()
		};
		// `eq` has no parameters of its own, so the impl's arguments, concrete
		// because the subject is, are the method's.
		let callee = self.instance(function, &args);
		let callee_id = self.enqueue_from(state, callee, span)?;
		// The checked signature's count; nothing about the callee is
		// lowered for it.
		let param_count = self.sema.functions[usize::from(callee.function)]
			.param_types
			.len();
		if param_count != 2 {
			self.unsupported(
				state.file_id,
				span,
				"an equality method that is not a binary function",
			)?;
			unreachable!()
		}
		let left = self.projection_value(state, subject);
		Ok(self.build_call(
			state,
			callee_id,
			vec![left, value],
			mir::ValueType::I32,
		))
	}

	/// The actions that bind a pattern's names, in pattern order. Shared by
	/// match arms, where it runs only on the branch whose condition matched,
	/// and by `local` declarations, whose irrefutable pattern always binds.
	fn collect_bindings(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		pattern: PatIdx,
		subject: Projection,
		out: &mut Vec<mir::ExprId>,
	) -> Result<(), ()> {
		match body.pattern(pattern) {
			PatternKind::Wildcard
			| PatternKind::Int(_)
			| PatternKind::Char(_)
			| PatternKind::Constant { .. }
			| PatternKind::AbstractConstant { .. }
			| PatternKind::Error => Ok(()),
			PatternKind::Bind(local) => {
				let value = self.projection_value(state, subject);
				let run = state.local_map[usize::from(local)];
				out.push(self.write_locals(state, run, value));
				Ok(())
			}
			PatternKind::Tuple(children) => {
				for (at, &child) in body.patterns(children).iter().enumerate() {
					let child_ty = self.pattern_ty(body, state, child);
					let span = body.pattern_span(child);
					let child_subject = self.project_field(
						state,
						subject,
						FieldIdx::new(at as u32),
						child_ty,
						span,
					)?;
					self.collect_bindings(
						body,
						state,
						child,
						child_subject,
						out,
					)?;
				}
				Ok(())
			}
			PatternKind::Struct { fields, .. } => {
				let fields_ty = self.pattern_ty(body, state, fields);
				let subject = self.retype(
					state,
					subject,
					fields_ty,
					body.pattern_span(fields),
				)?;
				self.collect_bindings(body, state, fields, subject, out)
			}
			PatternKind::Or(alternatives) => {
				let action =
					self.lower_or_bindings(body, state, alternatives, subject)?;
				out.push(action);
				Ok(())
			}
		}
	}

	/// Bindings for one `Or` pattern. The alternatives bind the same locals,
	/// so after the arm matched, re-testing the (pure) conditions selects the
	/// first alternative that matched and runs its stores. The last
	/// alternative needs no test: if the arm matched, and every earlier
	/// alternative failed, the last one is the one that matched.
	fn lower_or_bindings(
		&mut self,
		body: &Body,
		state: &mut FunctionState,
		alternatives: PatternRange,
		subject: Projection,
	) -> Result<mir::ExprId, ()> {
		let alternatives = body.patterns(alternatives);
		let effective = alternatives
			.iter()
			.position(|&alternative| {
				self.pattern_irrefutable(body, alternative)
			})
			.map_or(alternatives.len(), |at| at + 1);
		let alternatives = &alternatives[..effective];
		let mut actions = Vec::with_capacity(alternatives.len());
		for &alternative in alternatives {
			let mut bindings = Vec::new();
			self.collect_bindings(
				body,
				state,
				alternative,
				subject,
				&mut bindings,
			)?;
			actions.push(Some(self.bindings_value(state, bindings)));
		}
		let mut result = actions
			.pop()
			.expect("an `Or` pattern has at least one alternative")
			.expect("each alternative has an action");
		for at in (0..alternatives.len() - 1).rev() {
			let action =
				actions[at].take().expect("each alternative has an action");
			let condition = self.lower_pattern_condition(
				body,
				state,
				alternatives[at],
				subject,
			)?;
			// A test that always holds is `true`, so the later alternatives,
			// already built, stay in the tree.
			let condition = condition.unwrap_or_else(|| state.boolean(true));
			result = state.push(
				mir::ExprKind::IfElse {
					condition,
					then: action,
					otherwise: Some(result),
				},
				mir::ValueType::Unit,
			);
		}
		Ok(result)
	}

	/// A binding prelude as one unit-typed expression. No bindings is a no-op
	/// (not an empty Wasm block).
	fn bindings_value(
		&mut self,
		state: &mut FunctionState,
		mut bindings: Vec<mir::ExprId>,
	) -> mir::ExprId {
		match bindings.len() {
			0 => state.push(mir::ExprKind::Noop, mir::ValueType::Unit),
			1 => bindings.pop().unwrap(),
			_ => {
				let statements = state.list(bindings);
				state.push(
					mir::ExprKind::Sequence { statements },
					mir::ValueType::Unit,
				)
			}
		}
	}

	/// A projection of one field of `subject`. `child_ty` is the TIR type the
	/// field's pattern was checked against.
	fn project_field(
		&mut self,
		state: &FunctionState,
		subject: Projection,
		field: FieldIdx,
		child_ty: TypeIndex,
		span: TextSpan,
	) -> Result<Projection, ()> {
		let range = self.field_range(subject.tir_ty, state, field, span)?;
		let ty = self.lower_type(child_ty, state.file_id, span)?;
		debug_assert_eq!(
			range.len as usize,
			self.signatures.scalars(&ty).len(),
			"a field's pattern type and flat range agree"
		);
		let start = subject.range.start + range.start;
		Ok(Projection {
			root: subject.root,
			range: ScalarRange::new(start, range.len),
			ty,
			tir_ty: child_ty,
		})
	}

	/// The same value under another TIR type whose flat representation is
	/// the same. A struct's fields tuple is laid out exactly like the struct
	/// itself (declaration order, zero-sized fields omitted), so a `Struct`
	/// pattern can recurse into its `fields` pattern through this.
	fn retype(
		&mut self,
		state: &FunctionState,
		subject: Projection,
		tir_ty: TypeIndex,
		span: TextSpan,
	) -> Result<Projection, ()> {
		let ty = self.lower_type(tir_ty, state.file_id, span)?;
		debug_assert_eq!(
			subject.range.len as usize,
			self.signatures.scalars(&ty).len(),
			"a pattern's fields type has the same flat shape as its parent"
		);
		Ok(Projection {
			ty,
			tir_ty,
			..subject
		})
	}

	/// Read a projection as a MIR value: the locals of its scalars.
	fn projection_value(
		&self,
		state: &mut FunctionState,
		subject: Projection,
	) -> mir::ExprId {
		let run = subject.root.slice(subject.range);
		self.read_locals(state, run, subject.ty)
	}

	/// `subject == constant`, as a boolean.
	fn scalar_test(
		&self,
		state: &mut FunctionState,
		subject: Projection,
		value: i64,
	) -> mir::ExprId {
		let lhs = self.projection_value(state, subject);
		let rhs = state.push(mir::ExprKind::Int { value }, subject.ty);
		state.push(
			mir::ExprKind::Compare {
				op: mir::CompareOp::Eq,
				lhs,
				rhs,
			},
			mir::ValueType::I32,
		)
	}
}

/// An integer pattern's discriminant, canonical in the selector's Wasm
/// scalar. TIR stores int patterns as masked bits, so signed narrow types
/// need sign extension before they compare with a runtime value.
fn pattern_int_discriminant(bits: u64, primitive: Primitive) -> Option<i64> {
	Some(match primitive {
		Primitive::I8 => (bits as u8 as i8 as i32) as i64,
		Primitive::I16 => (bits as u16 as i16 as i32) as i64,
		Primitive::U8 | Primitive::U16 | Primitive::U32 | Primitive::I32 => {
			(bits as u32 as i32) as i64
		}
		Primitive::U64 | Primitive::I64 => bits as i64,
		Primitive::F32 | Primitive::F64 => return None,
	})
}

/// A constant pattern's discriminant. The evaluator already holds signed
/// narrow values sign-extended, so only the 32-bit scalar truncation is
/// needed before comparing.
fn constant_int_discriminant(bits: u64, ty: mir::ValueType) -> Option<i64> {
	Some(match ty {
		mir::ValueType::I32 => (bits as u32 as i32) as i64,
		mir::ValueType::I64 => bits as i64,
		_ => return None,
	})
}

fn and_conditions(
	state: &mut FunctionState,
	left: Option<mir::ExprId>,
	right: Option<mir::ExprId>,
) -> Option<mir::ExprId> {
	combine(state, mir::BinaryOp::And, left, right)
}

fn or_conditions(
	state: &mut FunctionState,
	left: Option<mir::ExprId>,
	right: Option<mir::ExprId>,
) -> Option<mir::ExprId> {
	combine(state, mir::BinaryOp::Or, left, right)
}

/// Two `Bool` conditions joined by `op`, either of which may be absent (one
/// that always holds). Both sides are pure tests, so neither needs to
/// short-circuit.
fn combine(
	state: &mut FunctionState,
	op: mir::BinaryOp,
	left: Option<mir::ExprId>,
	right: Option<mir::ExprId>,
) -> Option<mir::ExprId> {
	match (left, right) {
		(None, right) => right,
		(left, None) => left,
		(Some(lhs), Some(rhs)) => {
			Some(state.push(
				mir::ExprKind::Binary { op, lhs, rhs },
				mir::ValueType::I32,
			))
		}
	}
}
