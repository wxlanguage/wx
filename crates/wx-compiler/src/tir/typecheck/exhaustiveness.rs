//! Exhaustiveness and unreachable arms: a match's patterns, lowered for the
//! usefulness pass (`tir::usefulness`), and what it finds, reported.
//!
//! A constant compares as its value when it is one number, else it is
//! opaque: it is compared by its type's `Eq`, covers nothing but itself, and
//! a match naming it still needs `_`. Each opaque constant of a match is given
//! an identity (`OpaqueKey`), so that the same one written twice is found
//! unreachable. An enum whose variants have no value is unlisted. A constant's
//! body is built before any value exists, so its matches are decided once they
//! do (`ExprObligation::Match`).

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::{BodyContext, Integer};
use crate::diagnostics::DiagnosticCode;
use crate::tir::body::{ExprIdx, ExprKind, PatIdx, PatternKind, PatternRange};
use crate::tir::decls::{ConstIdx, EnumIdx};
use crate::tir::eval::ConstScalar;
use crate::tir::signatures::Semantics;
use crate::tir::types::{GenericArgs, Type, TypeIndex};
use crate::tir::usefulness::{
	Ctor, CtorSet, PatId, Patterns, Shapes, Usefulness, Witness,
};

/// How many missing patterns a non-exhaustive match names.
const SHOWN_WITNESSES: usize = 3;

/// An opaque constant as its pattern names it: the constant and its type
/// arguments (`[Self]` for a trait's declaration). What makes two of a match
/// the same test is `same`'s to decide. The usefulness pass sees only its
/// position in the match's table (`Ctor::Opaque`).
#[derive(Clone, Copy)]
struct OpaqueKey {
	constant: ConstIdx,
	type_args: GenericArgs,
}

impl OpaqueKey {
	/// Whether two are one test. Two with values are when their values are,
	/// whatever they are named: `eq` is called with the same arguments.
	/// Otherwise they are when they are the same constant of the same
	/// arguments, which has one value even where it is not known; arguments
	/// are compared by their types, since each pattern holds its own list. A
	/// constant either has a value or not, so a pair of one with a value and
	/// one without is two constants, and not the same.
	fn same(self, other: OpaqueKey, sema: &Semantics) -> bool {
		match (self.value(sema), other.value(sema)) {
			(Some(a), Some(b)) => a == b,
			_ => {
				let args = &sema.generic_args;
				self.constant == other.constant
					&& args.types(self.type_args) == args.types(other.type_args)
			}
		}
	}

	/// Its value, from the solver's memo, when it has no arguments and has
	/// been evaluated.
	fn value(self, sema: &Semantics) -> Option<&[ConstScalar]> {
		match self.type_args.is_empty() {
			true => sema.evaluated_value(self.constant),
			false => None,
		}
	}
}

/// One match's patterns, as `lower_pattern` builds them for the usefulness
/// pass: its arena, the identities of its opaque constants, whose positions
/// are the ids `Ctor::Opaque` holds, and the pattern each `|` was lowered
/// from, to point at its alternatives.
struct MatchPatterns {
	arena: Patterns,
	opaque: Vec<OpaqueKey>,
	ors: Vec<(PatId, PatIdx)>,
}

impl BodyContext<'_> {
	/// Reports each arm of `expr`, a `match`, that the arms before it cover,
	/// each alternative of an `|` that the arms and alternatives before it
	/// cover, and the values no arm matches. A match with a pattern that failed to
	/// check is left alone: what failed has said why. Decided as an
	/// `ExprObligation`, since an arm may compare with a constant's value.
	pub(super) fn check_match_usefulness(&mut self, expr: ExprIdx) {
		let ExprKind::Match { scrutinee, arms } = self.body.kind(expr) else {
			unreachable!("usefulness is a match's")
		};
		let ty = self.body.ty(scrutinee);
		if self.sema.types.has_error(ty) {
			return;
		}
		let mut pats = MatchPatterns {
			arena: Patterns::new(),
			opaque: Vec::new(),
			ors: Vec::new(),
		};
		let count = self.body.arms(arms).len();
		let mut lowered = Vec::with_capacity(count);
		for at in 0..count {
			let pattern = self.body.arms(arms)[at].pattern;
			let Some(pattern) = self.lower_pattern(pattern, &mut pats) else {
				return;
			};
			lowered.push(pattern);
		}
		let MatchPatterns { arena, ors, .. } = pats;
		let analysis = Usefulness::new(self, &arena).analyse(
			&lowered,
			ty,
			SHOWN_WITNESSES + 1,
		);
		// Arms and alternatives, reported in source order.
		let mut unreachable: Vec<(PatIdx, bool)> = analysis
			.unreachable_arms()
			.into_iter()
			.map(|at| (self.body.arms(arms)[at].pattern, true))
			.collect();
		for alternative in analysis.unreachable_alternatives() {
			let (_, or) = ors
				.iter()
				.find(|(id, _)| *id == alternative.or)
				.expect("every `|` is recorded where it is lowered");
			let PatternKind::Or(alternatives) = self.body.pattern(*or) else {
				unreachable!("an `|` is lowered from an `|` pattern")
			};
			let pattern =
				self.body.patterns(alternatives)[alternative.index as usize];
			unreachable.push((pattern, false));
		}
		unreachable
			.sort_by_key(|&(pattern, _)| self.body.pattern_span(pattern).start);
		for (pattern, is_arm) in unreachable {
			let span = self.body.pattern_span(pattern);
			let (message, label) = match is_arm {
				true => (
					"unreachable match arm",
					"the arms before it match every value this does",
				),
				false => (
					"unreachable pattern",
					"the arms and alternatives before it match every value \
					 this does",
				),
			};
			self.sema.diagnostics.push(
				Diagnostic::warning()
					.with_code(DiagnosticCode::UnreachableMatchArm.code())
					.with_message(message)
					.with_label(
						Label::primary(self.scope.file_id, span)
							.with_message(label),
					),
			);
		}
		let missing = analysis.missing;
		if missing.is_empty() {
			return;
		}
		let shown: Vec<String> = missing
			.iter()
			.take(SHOWN_WITNESSES)
			.map(|witness| format!("`{}`", self.render_witness(witness)))
			.collect();
		let listed = match &*shown {
			[one] => format!("pattern {one}"),
			[init @ .., last] => {
				let more = if missing.len() > SHOWN_WITNESSES {
					" and more"
				} else {
					""
				};
				if more.is_empty() {
					format!("patterns {} and {last}", init.join(", "))
				} else {
					format!("patterns {}, {last}{more}", init.join(", "))
				}
			}
			[] => unreachable!(),
		};
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::NonExhaustiveMatch.code())
				.with_message(format!(
					"non-exhaustive match: {listed} not covered"
				))
				.with_label(
					self.source_span(scrutinee)
						.primary_label()
						.with_message(format!("{listed} not covered")),
				)
				.with_note(
					"add an arm for them, or `_` to match everything else",
				),
		);
	}

	/// `pattern` as the usefulness pass sees it, pushed into the match's
	/// arena; `None` when it holds a pattern that failed to check.
	fn lower_pattern(
		&mut self,
		pattern: PatIdx,
		pats: &mut MatchPatterns,
	) -> Option<PatId> {
		let ty = self.body.pattern_ty(pattern);
		Some(match self.body.pattern(pattern) {
			PatternKind::Wildcard | PatternKind::Bind(_) => Patterns::WILD,
			// A struct is split as its fields' tuple; a lone field's value is
			// not one, so it is the struct's one child.
			PatternKind::Struct {
				struct_index,
				fields,
			} => {
				let fields = self.lower_pattern(fields, pats)?;
				let count = self.sema.structs[usize::from(struct_index)]
					.field_types
					.len();
				if count == 1 {
					pats.arena.ctor(Ctor::Single, &[fields])
				} else {
					fields
				}
			}
			PatternKind::Tuple(children) => {
				let children = self.lower_patterns(children, pats)?;
				pats.arena.ctor(Ctor::Single, &children)
			}
			PatternKind::Int(bits) => pats.arena.ctor(Ctor::Value(bits), &[]),
			// `Char` is a struct of its code point, which is what a char
			// pattern compares.
			PatternKind::Char(c) if ty == TypeIndex::CHAR => {
				let code = pats.arena.ctor(Ctor::Value(u64::from(c)), &[]);
				pats.arena.ctor(Ctor::Single, &[code])
			}
			PatternKind::Char(c) => {
				pats.arena.ctor(Ctor::Value(u64::from(c)), &[])
			}
			PatternKind::Constant {
				constant,
				type_args,
			} => match self.pattern_constant_value(constant, type_args, ty) {
				Some(bits) if ty == TypeIndex::CHAR => {
					let code = pats.arena.ctor(Ctor::Value(bits), &[]);
					pats.arena.ctor(Ctor::Single, &[code])
				}
				Some(bits) => pats.arena.ctor(Ctor::Value(bits), &[]),
				None => self.opaque_pattern(constant, type_args, pats),
			},
			PatternKind::AbstractConstant {
				constant,
				type_args,
			} => self.opaque_pattern(constant, type_args, pats),
			PatternKind::Or(alternatives) => {
				let lowered = self.lower_patterns(alternatives, pats)?;
				let or = pats.arena.or(&lowered);
				pats.ors.push((or, pattern));
				or
			}
			PatternKind::Error => return None,
		})
	}

	/// Each pattern of `list`, lowered; `None` when one failed to check.
	fn lower_patterns(
		&mut self,
		list: PatternRange,
		pats: &mut MatchPatterns,
	) -> Option<Vec<PatId>> {
		(0..self.body.patterns(list).len())
			.map(|at| {
				let pattern = self.body.patterns(list)[at];
				self.lower_pattern(pattern, pats)
			})
			.collect()
	}

	/// An opaque constant, its id the position of its identity in the match's
	/// table, added there if it is the first of its identity in the match.
	fn opaque_pattern(
		&mut self,
		constant: ConstIdx,
		type_args: GenericArgs,
		pats: &mut MatchPatterns,
	) -> PatId {
		// Evaluated first, so that `same` can read its value; one that has
		// none is compared as the constant it is.
		if type_args.is_empty() {
			let _ = self.sema.const_value(self.strings, constant);
		}
		let key = OpaqueKey {
			constant,
			type_args,
		};
		let sema = &*self.sema;
		let opaque = &mut pats.opaque;
		let at = match opaque.iter().position(|known| known.same(key, sema)) {
			Some(at) => at,
			None => {
				opaque.push(key);
				opaque.len() - 1
			}
		};
		pats.arena.ctor(Ctor::Opaque(at as u32), &[])
	}

	/// The value a constant of type `ty` compares as, when this body can
	/// evaluate it and it is one of the values `ty`'s set lists or counts.
	fn pattern_constant_value(
		&mut self,
		constant: ConstIdx,
		type_args: GenericArgs,
		ty: TypeIndex,
	) -> Option<u64> {
		if !type_args.is_empty() {
			return None;
		}
		let bits = self.pattern_bits(constant)?;
		match Integer::from_type(ty) {
			Some(integer) => Some(bits & integer.mask()),
			None => match *self.sema.types.resolve(ty) {
				Type::Enum { .. } => Some(bits),
				_ if ty == TypeIndex::CHAR => Some(bits),
				_ => None,
			},
		}
	}

	/// A constant's value as a pattern compares with it; `None` when it has
	/// none (it is opaque to the match).
	fn pattern_bits(&mut self, constant: ConstIdx) -> Option<u64> {
		self.sema
			.constant_bits(self.strings, constant)
			.ok()
			.flatten()
	}

	/// The value of each of an enum's variants, in written order, each once;
	/// `None` when one has no value here.
	fn variant_values(&mut self, enum_index: EnumIdx) -> Option<Vec<u64>> {
		let variants = self.sema.decls.enums[usize::from(enum_index)]
			.variants
			.clone();
		let mut values = Vec::new();
		for at in u32::from(variants.start)..u32::from(variants.end) {
			let bits = self.pattern_bits(ConstIdx::new(at))?;
			if !values.contains(&bits) {
				values.push(bits);
			}
		}
		Some(values)
	}

	/// A witness as it would be written in a pattern.
	fn render_witness(&mut self, witness: &Witness) -> String {
		let Witness::Ctor { ctor, ty, fields } = witness else {
			return "_".to_string();
		};
		let ty = *ty;
		if ty == TypeIndex::CHAR {
			return match fields.as_slice() {
				[
					Witness::Ctor {
						ctor: Ctor::Value(bits),
						..
					},
				] => char::from_u32(*bits as u32)
					.map_or_else(|| "_".to_string(), |c| format!("{c:?}")),
				_ => "_".to_string(),
			};
		}
		let fields: Vec<String> = fields
			.iter()
			.map(|field| self.render_witness(field))
			.collect();
		let Ctor::Value(bits) = *ctor else {
			return match *self.sema.types.resolve(ty) {
				Type::Struct { struct_index, .. } => {
					let name = self.sema.decls.name(struct_index).inner;
					let name = self.strings.resolve(name).unwrap();
					format!("{name}({})", fields.join(", "))
				}
				_ => format!("({})", fields.join(", ")),
			};
		};
		if let Some(integer) = Integer::from_type(ty) {
			if integer.is_signed() {
				let shift = 64 - integer.mask().count_ones();
				return (((bits << shift) as i64) >> shift).to_string();
			}
			return bits.to_string();
		}
		if let Type::Enum { enum_index } = *self.sema.types.resolve(ty) {
			let decl = &self.sema.decls.enums[usize::from(enum_index)];
			let (enum_name, variants) = (
				self.sema.decls.item(decl.loc).name.inner,
				decl.variants.clone(),
			);
			for at in u32::from(variants.start)..u32::from(variants.end) {
				let constant = ConstIdx::new(at);
				if self.pattern_bits(constant) == Some(bits) {
					let variant = self.sema.decls.name(constant).inner;
					return format!(
						"{}::{}",
						self.strings.resolve(enum_name).unwrap(),
						self.strings.resolve(variant).unwrap()
					);
				}
			}
		}
		"_".to_string()
	}
}

impl Shapes for BodyContext<'_> {
	fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet {
		if ty == TypeIndex::NEVER {
			return CtorSet::Empty;
		}
		if let Some(integer) = Integer::from_type(ty) {
			return CtorSet::Counted {
				count: u128::from(integer.mask()) + 1,
			};
		}
		match *self.sema.types.resolve(ty) {
			Type::Tuple { .. } | Type::Struct { .. } => CtorSet::Single,
			Type::Enum { enum_index } => {
				match self.variant_values(enum_index) {
					Some(values) => CtorSet::Listed(values),
					None => CtorSet::Unlisted,
				}
			}
			_ => CtorSet::Unlisted,
		}
	}

	fn fields(&mut self, ty: TypeIndex) -> Vec<TypeIndex> {
		match *self.sema.types.resolve(ty) {
			Type::Tuple { elements } => self.sema.types.list(elements).to_vec(),
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let type_args = self.sema.types.list(type_args).to_vec();
				let count = self.sema.structs[usize::from(struct_index)]
					.field_types
					.len();
				(0..count)
					.map(|field| {
						self.field_type(struct_index, &type_args, field)
					})
					.collect()
			}
			_ => unreachable!("only a tuple or a struct has fields"),
		}
	}
}
