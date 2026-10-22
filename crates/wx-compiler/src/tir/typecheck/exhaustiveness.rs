//! Exhaustiveness and unreachable arms: a match's patterns, lowered for the
//! usefulness pass (`tir::usefulness`), and what it finds, reported.
//!
//! A constant compares as its value when it is one number this body can
//! evaluate, else it is opaque: it covers nothing but itself, so a match
//! naming it still needs `_`. A constant's value is known wherever a pattern
//! may name it, a function's block or an initializer's alike; one that is
//! still being built, or that `eval` cannot reduce to a number, is opaque,
//! and an enum whose variants have no value is unlisted.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::{BodyContext, Integer};
use crate::diagnostics::DiagnosticCode;
use crate::tir::body::{Arm, ExprIdx, PatIdx, PatternKind};
use crate::tir::defs::{ConstIdx, EnumIdx};
use crate::tir::types::{Type, TypeIndex, TypeList};
use crate::tir::usefulness::{Ctor, CtorSet, Pat, Shapes, Witness, witnesses};

/// How many missing patterns a non-exhaustive match names.
const SHOWN_WITNESSES: usize = 3;

impl BodyContext<'_, '_, '_, '_> {
	/// Reports each arm the arms before it cover, and the values no arm
	/// matches. A match with a pattern that failed to check is left alone:
	/// what failed has said why.
	pub(super) fn check_match_usefulness(
		&mut self,
		scrutinee: ExprIdx,
		arms: &[Arm],
	) {
		let ty = self.body.ty(scrutinee);
		if self.cx.types.has_error(ty) {
			return;
		}
		let mut rows = Vec::with_capacity(arms.len());
		for arm in arms {
			let Some(pattern) = self.lower_pattern(arm.pattern) else {
				return;
			};
			rows.push(vec![pattern]);
		}
		for (at, arm) in arms.iter().enumerate() {
			if witnesses(self, &rows[..at], &rows[at], &[ty], 1).is_empty() {
				let span = self.body.pattern_span(arm.pattern);
				self.cx.diagnostics.push(
					Diagnostic::warning()
						.with_code(DiagnosticCode::UnreachableMatchArm.code())
						.with_message("unreachable match arm")
						.with_label(
							Label::primary(self.scope.file_id, span)
								.with_message(
									"the arms before it match every value \
									 this does",
								),
						),
				);
			}
		}
		let missing =
			witnesses(self, &rows, &[Pat::Wild], &[ty], SHOWN_WITNESSES + 1);
		if missing.is_empty() {
			return;
		}
		let shown: Vec<String> = missing
			.iter()
			.take(SHOWN_WITNESSES)
			.map(|row| format!("`{}`", self.render_witness(&row[0])))
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
		self.cx.diagnostics.push(
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

	/// `pattern` as the usefulness pass sees it; `None` when it holds a
	/// pattern that failed to check.
	fn lower_pattern(&mut self, pattern: PatIdx) -> Option<Pat> {
		let ty = self.body.pattern_ty(pattern);
		let value = |value: u64| Pat::Ctor(Ctor::Value(value), Vec::new());
		Some(match self.body.pattern(pattern) {
			PatternKind::Wildcard | PatternKind::Bind(_) => Pat::Wild,
			PatternKind::Tuple(children)
			| PatternKind::Struct {
				fields: children, ..
			} => {
				let children = self.body.patterns(children).to_vec();
				let mut lowered = Vec::with_capacity(children.len());
				for child in children {
					lowered.push(self.lower_pattern(child)?);
				}
				Pat::Ctor(Ctor::Single, lowered)
			}
			PatternKind::Int(bits) => value(bits),
			PatternKind::Bool(bit) => value(u64::from(bit)),
			PatternKind::Char(c) => value(u64::from(c)),
			PatternKind::Constant {
				constant,
				type_args,
			} => match self.pattern_constant_value(constant, type_args, ty) {
				Some(bits) => value(bits),
				None => Pat::Ctor(Ctor::Opaque, Vec::new()),
			},
			PatternKind::AbstractConstant { .. } => {
				Pat::Ctor(Ctor::Opaque, Vec::new())
			}
			PatternKind::Or(alternatives) => {
				let alternatives = self.body.patterns(alternatives).to_vec();
				let mut lowered = Vec::with_capacity(alternatives.len());
				for alternative in alternatives {
					lowered.push(self.lower_pattern(alternative)?);
				}
				Pat::Or(lowered)
			}
			PatternKind::Error => return None,
		})
	}

	/// The value a constant of type `ty` compares as, when this body can
	/// evaluate it and it is one of the values `ty`'s set lists or counts.
	fn pattern_constant_value(
		&mut self,
		constant: ConstIdx,
		type_args: TypeList,
		ty: TypeIndex,
	) -> Option<u64> {
		if !self.cx.types.list(type_args).is_empty() {
			return None;
		}
		let bits = self.cx.constant_bits(constant)?;
		match Integer::from_type(ty) {
			Some(integer) => Some(bits & integer.mask()),
			None => match *self.cx.types.resolve(ty) {
				Type::Enum { .. } => Some(bits),
				_ if ty == TypeIndex::BOOL || ty == TypeIndex::CHAR => {
					Some(bits)
				}
				_ => None,
			},
		}
	}

	/// The value of each of an enum's variants, in written order, each once;
	/// `None` when one has no value here.
	fn variant_values(&mut self, enum_index: EnumIdx) -> Option<Vec<u64>> {
		let variants =
			self.cx.defs.enums[usize::from(enum_index)].variants.clone();
		let mut values = Vec::new();
		for at in u32::from(variants.start)..u32::from(variants.end) {
			let bits = self.cx.constant_bits(ConstIdx::new(at))?;
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
		let fields: Vec<String> = fields
			.iter()
			.map(|field| self.render_witness(field))
			.collect();
		let Ctor::Value(bits) = *ctor else {
			return match *self.cx.types.resolve(ty) {
				Type::Struct { struct_index, .. } => {
					let name = self.cx.defs.structs[usize::from(struct_index)]
						.name
						.inner;
					let name = self.cx.strings.resolve(name).unwrap();
					format!("{name}({})", fields.join(", "))
				}
				_ => format!("({})", fields.join(", ")),
			};
		};
		if ty == TypeIndex::BOOL {
			return (bits != 0).to_string();
		}
		if ty == TypeIndex::CHAR {
			return char::from_u32(bits as u32)
				.map_or_else(|| "_".to_string(), |c| format!("{c:?}"));
		}
		if let Some(integer) = Integer::from_type(ty) {
			if integer.is_signed() {
				let shift = 64 - integer.mask().count_ones();
				return (((bits << shift) as i64) >> shift).to_string();
			}
			return bits.to_string();
		}
		if let Type::Enum { enum_index } = *self.cx.types.resolve(ty) {
			let def = &self.cx.defs.enums[usize::from(enum_index)];
			let (enum_name, variants) = (def.name.inner, def.variants.clone());
			for at in u32::from(variants.start)..u32::from(variants.end) {
				let constant = ConstIdx::new(at);
				if self.cx.constant_bits(constant) == Some(bits) {
					let variant =
						self.cx.defs.constants[at as usize].name.inner;
					return format!(
						"{}::{}",
						self.cx.strings.resolve(enum_name).unwrap(),
						self.cx.strings.resolve(variant).unwrap()
					);
				}
			}
		}
		"_".to_string()
	}
}

impl Shapes for BodyContext<'_, '_, '_, '_> {
	fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet {
		if ty == TypeIndex::BOOL {
			return CtorSet::Listed(vec![0, 1]);
		}
		if ty == TypeIndex::CHAR {
			return CtorSet::Counted {
				// Every scalar value but the surrogates.
				count: 0x11_0000 - 0x800,
				valid: |value| {
					u32::try_from(value)
						.is_ok_and(|v| char::from_u32(v).is_some())
				},
			};
		}
		if ty == TypeIndex::NEVER {
			return CtorSet::Empty;
		}
		if let Some(integer) = Integer::from_type(ty) {
			return CtorSet::Counted {
				count: u128::from(integer.mask()) + 1,
				valid: |_| true,
			};
		}
		match *self.cx.types.resolve(ty) {
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
		match *self.cx.types.resolve(ty) {
			Type::Tuple { elements } => self.cx.types.list(elements).to_vec(),
			Type::Struct {
				struct_index,
				type_args,
			} => {
				let type_args = self.cx.types.list(type_args).to_vec();
				let count = self.cx.structs[usize::from(struct_index)]
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
