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

use super::{Body, ExprIdx, FunctionState, Lowerer, mir};
use crate::ast::BinaryOp;
use crate::diagnostics::TextSpan;
use crate::tir::body::{
	Arm, ArmRange, ExprKind, PatIdx, PatternKind, PatternRange,
};
use crate::tir::defs::{ConstIdx, FieldIdx, MemberKind};
use crate::tir::members::{TraitImplLookup, TraitMemberSelection};
use crate::tir::types::{TypeIndex, TypeList};

/// A value of the match scrutinee at some field path, read from one root
/// local. `range` is a flat scalar range in that local and `tir_ty` says what
/// the range means (so nested projections can be computed without keeping a
/// separate type stack).
#[derive(Clone, Copy)]
struct Projection {
	local_index: mir::LocalIndex,
	range: mir::ScalarRange,
	ty: mir::ValueType,
	tir_ty: TypeIndex,
}

impl Lowerer<'_, '_, '_, '_> {
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
	) -> Result<mir::Expression, ()> {
		// A diverging initializer means no binding runs; keep its `Never`.
		if ty == mir::ValueType::Never {
			let value = self.lower_expr(body, state, value)?;
			debug_assert_eq!(value.ty, mir::ValueType::Never);
			return Ok(value);
		}
		match body.pattern(pattern) {
			PatternKind::Wildcard => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				return Ok(mir::Expression {
					kind: mir::ExprKind::Drop { value },
					ty: mir::ValueType::Unit,
				});
			}
			PatternKind::Bind(local) => {
				let value = Box::new(self.lower_expr(body, state, value)?);
				return Ok(mir::Expression {
					kind: mir::ExprKind::LocalSet {
						local_index: state.local_map[usize::from(local)],
						value,
					},
					ty: mir::ValueType::Unit,
				});
			}
			_ => {}
		}

		debug_assert!(
			self.pattern_irrefutable(body, pattern),
			"a local pattern always matches"
		);
		let value_ty = self.lower_type(
			body.ty(value),
			state.env,
			state.file_id,
			body.span(value),
		)?;
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
	) -> Result<mir::Expression, ()> {
		let scrutinee_ty = self.lower_type(
			body.ty(scrutinee),
			state.env,
			state.file_id,
			body.span(scrutinee),
		)?;
		// A diverging scrutinee means no arm runs. Keeping the scrutinee's
		// `Never` value makes the match diverge too; the arms' checked result
		// types are irrelevant on that path.
		if scrutinee_ty == mir::ValueType::Never {
			let value = self.lower_expr(body, state, scrutinee)?;
			debug_assert_eq!(value.ty, mir::ValueType::Never);
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

		if let Some(discriminants) =
			self.switch_discriminants(body, arms, scrutinee_ty)
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
	) -> Option<Vec<Option<i64>>> {
		// `Switch` compares integer discriminants. Floats have no canonical
		// integer selector here, so they take the decision tree instead.
		if !matches!(
			ty,
			mir::ValueType::I32
				| mir::ValueType::U32
				| mir::ValueType::I8
				| mir::ValueType::U8
				| mir::ValueType::I16
				| mir::ValueType::U16
				| mir::ValueType::I64
				| mir::ValueType::U64
				| mir::ValueType::Bool
		) {
			return None;
		}
		let mut discriminants = Vec::with_capacity(arms.len());
		for arm in arms {
			let discriminant = match body.pattern(arm.pattern) {
				PatternKind::Int(bits) => {
					Some(pattern_int_discriminant(bits, ty)?)
				}
				PatternKind::Constant {
					constant,
					type_args,
				} => {
					if !type_args.is_empty() {
						return None;
					}
					match self.context.constant_bits(constant) {
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
	) -> Result<mir::Expression, ()> {
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
			(
				mir::Expression {
					kind: mir::ExprKind::LocalGet {
						local_index: subject.local_index,
					},
					ty: scrutinee_ty,
				},
				Some(subject),
			)
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
					let value = self.lower_expr(body, state, arm.body)?;
					let value = self.block_for_branch(state, value);
					cases.push((*discriminant, value));
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
						let set = mir::Expression {
							kind: mir::ExprKind::LocalSet {
								local_index: state.local_map
									[usize::from(local)],
								value: Box::new(bind),
							},
							ty: mir::ValueType::Unit,
						};
						self.sequence(state, vec![set], value)
					}
					_ => value,
				};
				Some(Box::new(self.block_for_branch(state, value)))
			}
			None => None,
		};

		let switch = mir::Expression {
			kind: mir::ExprKind::Switch {
				selector: Box::new(selector),
				cases: cases.into_boxed_slice(),
				default,
			},
			ty,
		};
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
	) -> Result<mir::Expression, ()> {
		let (subject, prefix) =
			self.lower_subject(body, state, scrutinee, scrutinee_ty)?;
		let mut result = unreachable();
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
			result = match condition {
				// An irrefutable arm's body is the tree's base; earlier
				// arms still wrap it.
				None => value,
				Some(condition) => {
					let then_block = self.block_for_branch(state, value);
					let else_block = self.block_for_branch(state, result);
					mir::Expression {
						kind: mir::ExprKind::IfElse {
							condition: Box::new(condition),
							then_block: Box::new(then_block),
							else_block: Some(Box::new(else_block)),
						},
						ty,
					}
				}
			};
		}
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
	) -> Result<(Projection, Vec<mir::Expression>), ()> {
		let tir_ty = body.ty(scrutinee);
		let (local_index, prefix) = match body.kind(scrutinee) {
			ExprKind::Local(local) => {
				(state.local_map[usize::from(local)], Vec::new())
			}
			_ => {
				let value = self.lower_expr(body, state, scrutinee)?;
				let local_index = self.push_temp_local(state, ty);
				let prefix = vec![mir::Expression {
					kind: mir::ExprKind::LocalSet {
						local_index,
						value: Box::new(value),
					},
					ty: mir::ValueType::Unit,
				}];
				(local_index, prefix)
			}
		};
		let len = self.slot_count(ty) as u32;
		Ok((
			Projection {
				local_index,
				range: mir::ScalarRange::new(0, len),
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
	) -> Result<Option<mir::Expression>, ()> {
		match body.pattern(pattern) {
			PatternKind::Wildcard | PatternKind::Bind(_) => Ok(None),
			PatternKind::Tuple(children) => {
				let mut condition = None;
				for (at, &child) in body.patterns(children).iter().enumerate() {
					let child_ty = body.pattern_ty(child);
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
					condition = and_conditions(condition, child_condition);
				}
				Ok(condition)
			}
			PatternKind::Struct { fields, .. } => {
				let fields_ty = body.pattern_ty(fields);
				let subject = self.retype(
					state,
					subject,
					fields_ty,
					body.pattern_span(fields),
				)?;
				self.lower_pattern_condition(body, state, fields, subject)
			}
			PatternKind::Int(bits) => {
				let Some(discriminant) =
					pattern_int_discriminant(bits, subject.ty)
				else {
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
					state.env,
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
				let Some(codepoint) =
					pattern_int_discriminant(u64::from(value), field.ty)
				else {
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
				let mut condition = None;
				for &alternative in alternatives {
					match self.lower_pattern_condition(
						body,
						state,
						alternative,
						subject,
					)? {
						// One alternative always matches, so the whole arm
						// does. Earlier alternatives still matter to the
						// binding selector, but not to this condition.
						None => return Ok(None),
						Some(next) => {
							condition = or_conditions(condition, Some(next));
						}
					}
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
		type_args: TypeList,
	) -> Result<Option<mir::Expression>, ()> {
		let span = body.pattern_span(pattern);
		if !type_args.is_empty() {
			self.unsupported(
				state.file_id,
				span,
				"an associated or generic constant pattern",
			)?;
			unreachable!()
		}
		let value = match self.context.const_value(constant) {
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
		if matches!(subject.ty, mir::ValueType::F32 | mir::ValueType::F64) {
			self.unsupported(
				state.file_id,
				span,
				"a float constant pattern (floats have no total equality)",
			)?;
			unreachable!()
		}
		if matches!(subject.ty, mir::ValueType::Aggregate { .. }) {
			let value = self.materialize_constant(
				state.file_id,
				span,
				subject.ty,
				&value,
			)?;
			return Ok(Some(self.equality_test(state, subject, value, span)?));
		}
		let [scalar] = value.as_slice() else {
			self.unsupported(
				state.file_id,
				span,
				"a scalar constant pattern with several values",
			)?;
			unreachable!()
		};
		let constant =
			self.constant_scalar(state.file_id, span, subject.ty, *scalar)?;
		let left = self.projection_value(state, subject);
		Ok(Some(mir::Expression {
			kind: mir::ExprKind::Eq {
				left: Box::new(left),
				right: Box::new(constant),
			},
			ty: mir::ValueType::Bool,
		}))
	}

	/// `subject == value` through the concrete `PartialEq::eq` impl that the
	/// pattern's checked `Eq` bound requires. An aggregate's equality is its
	/// impl's, not a field-by-field comparison, so a type may define equality
	/// that differs from its representation.
	fn equality_test(
		&mut self,
		state: &mut FunctionState,
		subject: Projection,
		value: mir::Expression,
		span: TextSpan,
	) -> Result<mir::Expression, ()> {
		let Some(method) = self.context.operators.binary(BinaryOp::Eq) else {
			self.unsupported(
				state.file_id,
				span,
				"an aggregate pattern without the `PartialEq` operator",
			)?;
			unreachable!()
		};
		let lookup = match self.context.find_trait_impl_query(
			state.env,
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
		if !args.is_empty() {
			self.unsupported(
				state.file_id,
				span,
				"an equality impl with type arguments",
			)?;
		}
		let TraitMemberSelection::Impl(
			MemberKind::Method(function) | MemberKind::Function(function),
		) = self
			.context
			.defs
			.select_trait_member(impl_index, MemberKind::Method(method.method))
		else {
			self.unsupported(
				state.file_id,
				span,
				"an equality method that the impl does not provide",
			)?;
			unreachable!()
		};
		let callee_id = self.enqueue(function);
		let (callee_signature, callee_params, ..) =
			self.lower_signature(function)?;
		if callee_params.len() != 2 {
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
			callee_signature,
			vec![left, value],
			mir::ValueType::Bool,
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
		out: &mut Vec<mir::Expression>,
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
				out.push(mir::Expression {
					kind: mir::ExprKind::LocalSet {
						local_index: state.local_map[usize::from(local)],
						value: Box::new(value),
					},
					ty: mir::ValueType::Unit,
				});
				Ok(())
			}
			PatternKind::Tuple(children) => {
				for (at, &child) in body.patterns(children).iter().enumerate() {
					let child_ty = body.pattern_ty(child);
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
				let fields_ty = body.pattern_ty(fields);
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
	) -> Result<mir::Expression, ()> {
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
			result = match condition {
				None => action,
				Some(condition) => {
					let then_block = self.block_for_branch(state, action);
					let else_block = self.block_for_branch(state, result);
					mir::Expression {
						kind: mir::ExprKind::IfElse {
							condition: Box::new(condition),
							then_block: Box::new(then_block),
							else_block: Some(Box::new(else_block)),
						},
						ty: mir::ValueType::Unit,
					}
				}
			};
		}
		Ok(result)
	}

	/// A binding prelude as one unit-typed expression. No bindings is a no-op
	/// (not an empty Wasm block).
	fn bindings_value(
		&mut self,
		state: &mut FunctionState,
		mut bindings: Vec<mir::Expression>,
	) -> mir::Expression {
		match bindings.len() {
			0 => mir::Expression {
				kind: mir::ExprKind::Noop,
				ty: mir::ValueType::Unit,
			},
			1 => bindings.pop().unwrap(),
			_ => {
				let scope_index =
					self.push_synthetic_scope(state, mir::ValueType::Unit);
				mir::Expression {
					kind: mir::ExprKind::Block {
						scope_index,
						expressions: bindings.into_boxed_slice(),
					},
					ty: mir::ValueType::Unit,
				}
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
		let ty = self.lower_type(child_ty, state.env, state.file_id, span)?;
		debug_assert_eq!(
			range.len as usize,
			self.slot_count(ty),
			"a field's pattern type and flat range agree"
		);
		let start = u32::from(subject.range.start) + u32::from(range.start);
		Ok(Projection {
			local_index: subject.local_index,
			range: mir::ScalarRange::new(start, range.len),
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
		let ty = self.lower_type(tir_ty, state.env, state.file_id, span)?;
		debug_assert_eq!(
			subject.range.len as usize,
			self.slot_count(ty),
			"a pattern's fields type has the same flat shape as its parent"
		);
		Ok(Projection {
			ty,
			tir_ty,
			..subject
		})
	}

	/// Read a projection as a MIR value. A whole-value read is a `LocalGet`;
	/// a field path is an `AggregateGet` over the root local's flat slots.
	fn projection_value(
		&self,
		state: &FunctionState,
		subject: Projection,
	) -> mir::Expression {
		if subject.ty == mir::ValueType::Unit {
			return mir::Expression {
				kind: mir::ExprKind::Noop,
				ty: mir::ValueType::Unit,
			};
		}
		let root_ty = state.locals[usize::from(subject.local_index)].ty;
		let whole = u32::from(subject.range.start) == 0
			&& subject.range.len as usize == self.slot_count(root_ty);
		if whole && subject.ty == root_ty {
			mir::Expression {
				kind: mir::ExprKind::LocalGet {
					local_index: subject.local_index,
				},
				ty: subject.ty,
			}
		} else {
			mir::Expression {
				kind: mir::ExprKind::AggregateGet {
					local_index: subject.local_index,
					range: subject.range,
				},
				ty: subject.ty,
			}
		}
	}

	/// `subject == constant`, as a boolean.
	fn scalar_test(
		&self,
		state: &FunctionState,
		subject: Projection,
		value: i64,
	) -> mir::Expression {
		let left = self.projection_value(state, subject);
		let right = mir::Expression {
			kind: mir::ExprKind::Int { value },
			ty: subject.ty,
		};
		mir::Expression {
			kind: mir::ExprKind::Eq {
				left: Box::new(left),
				right: Box::new(right),
			},
			ty: mir::ValueType::Bool,
		}
	}
}

/// An integer pattern's discriminant, canonical in the selector's Wasm
/// scalar. TIR stores int patterns as masked bits, so signed narrow types
/// need sign extension before they compare with a runtime value.
fn pattern_int_discriminant(bits: u64, ty: mir::ValueType) -> Option<i64> {
	Some(match ty {
		mir::ValueType::I8 => (bits as u8 as i8 as i32) as i64,
		mir::ValueType::I16 => (bits as u16 as i16 as i32) as i64,
		mir::ValueType::I32 => (bits as u32 as i32) as i64,
		mir::ValueType::I64 => bits as i64,
		mir::ValueType::U8 | mir::ValueType::U16 | mir::ValueType::U32 => {
			(bits as u32 as i32) as i64
		}
		mir::ValueType::U64 => bits as i64,
		mir::ValueType::Bool => (bits != 0) as i64,
		_ => return None,
	})
}

/// A constant pattern's discriminant. The evaluator already holds signed
/// narrow values sign-extended, so only the 32-bit scalar truncation is
/// needed before comparing.
fn constant_int_discriminant(bits: u64, ty: mir::ValueType) -> Option<i64> {
	Some(match ty {
		mir::ValueType::I8
		| mir::ValueType::U8
		| mir::ValueType::I16
		| mir::ValueType::U16
		| mir::ValueType::I32
		| mir::ValueType::U32
		| mir::ValueType::Bool => (bits as u32 as i32) as i64,
		mir::ValueType::I64 | mir::ValueType::U64 => bits as i64,
		_ => return None,
	})
}

fn and_conditions(
	left: Option<mir::Expression>,
	right: Option<mir::Expression>,
) -> Option<mir::Expression> {
	match (left, right) {
		(None, right) => right,
		(left, None) => left,
		(Some(left), Some(right)) => Some(mir::Expression {
			kind: mir::ExprKind::And {
				left: Box::new(left),
				right: Box::new(right),
			},
			ty: mir::ValueType::Bool,
		}),
	}
}

fn or_conditions(
	left: Option<mir::Expression>,
	right: Option<mir::Expression>,
) -> Option<mir::Expression> {
	match (left, right) {
		(None, right) => right,
		(left, None) => left,
		(Some(left), Some(right)) => Some(mir::Expression {
			kind: mir::ExprKind::Or {
				left: Box::new(left),
				right: Box::new(right),
			},
			ty: mir::ValueType::Bool,
		}),
	}
}

fn unreachable() -> mir::Expression {
	mir::Expression {
		kind: mir::ExprKind::Unreachable,
		ty: mir::ValueType::Never,
	}
}
