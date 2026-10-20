//! Usefulness: whether a pattern matches some value that none of the patterns
//! before it does. One question answers both checks a match needs: an arm is
//! unreachable when it is not useful after the arms before it, and a match is
//! non-exhaustive when `_` is still useful after all of them. The values that
//! make a pattern useful are its *witnesses*, which name what a
//! non-exhaustive match misses.
//!
//! This is the algorithm of Maranget's "Warnings for pattern matching", as
//! rustc's `rustc_pattern_analysis` implements it. Patterns are seen as
//! constructors applied to sub-patterns (`Pat`), rows of them as a matrix,
//! and each step looks at the first column only:
//!
//! - *Specialising* by a constructor `c` keeps the rows that can match `c`, and
//!   replaces their first pattern by its sub-patterns (a wildcard by as many
//!   wildcards).
//! - The *default* rows are the ones headed by a wildcard, without it: what is
//!   left to match a value whose constructor no row names.
//!
//! The module is pure: what a type's constructors are and what a constructor's
//! fields are is asked of a `Shapes`, which the checker implements.

use super::types::TypeIndex;

/// What a pattern matches at its root.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Ctor {
	/// The one constructor of a tuple or a struct, with one field per element
	/// or field.
	Single,
	/// A value of a type with many: a `bool` (`0`, `1`), an integer (its bits),
	/// a `char` (its code point), or an enum's variant (its discriminant's
	/// bits).
	Value(u64),
	/// A constant whose value is not known here (a trait's declaration, one
	/// that is not a single number): it matches some value, never a known set,
	/// so it covers nothing but itself.
	Opaque,
}

/// A pattern, as the algorithm sees it.
#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Pat {
	/// `_`, a binding, or anything that matches every value.
	Wild,
	Ctor(Ctor, Vec<Pat>),
	/// Alternatives, each its own row.
	Or(Vec<Pat>),
}

/// Every constructor of a type.
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum CtorSet {
	/// A tuple, a struct, `()`.
	Single,
	/// A finite set of values, all listed: `bool`'s, an enum's variants'.
	Listed(Vec<u64>),
	/// `count` values, in order from `0` up, too many to list: an integer's
	/// (by their bits), `char`'s (valid scalar values, by their code point).
	Counted { count: u128, valid: fn(u64) -> bool },
	/// No values at all (`!`): no arm is needed.
	Empty,
	/// Values no pattern can list (floats, pointers, type parameters): only a
	/// wildcard covers them.
	Unlisted,
}

/// What the algorithm asks of types.
pub(super) trait Shapes {
	fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet;
	/// The types of the fields of `ty`'s `Single` constructor.
	fn fields(&mut self, ty: TypeIndex) -> Vec<TypeIndex>;
}

/// A value no row matches, as a pattern: `Wild` stands for any value.
#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Witness {
	Wild,
	Ctor {
		ctor: Ctor,
		ty: TypeIndex,
		fields: Vec<Witness>,
	},
}

/// The values that match `q` and no row of `rows`, as rows of witnesses, one
/// per column, at most `limit` of them; empty when `q` is not useful. `types`
/// are the columns' types.
pub(super) fn witnesses(
	shapes: &mut dyn Shapes,
	rows: &[Vec<Pat>],
	q: &[Pat],
	types: &[TypeIndex],
	limit: usize,
) -> Vec<Vec<Witness>> {
	let rows = expand_or(rows);
	let Some((head, tail)) = q.split_first() else {
		return if rows.is_empty() {
			vec![Vec::new()]
		} else {
			Vec::new()
		};
	};
	let (ty, tail_types) = (types[0], &types[1..]);
	match head {
		Pat::Or(alternatives) => {
			let mut found = Vec::new();
			for alternative in alternatives {
				let mut q = vec![alternative.clone()];
				q.extend_from_slice(tail);
				let left = limit - found.len();
				found.extend(witnesses(shapes, &rows, &q, types, left));
				if found.len() >= limit {
					break;
				}
			}
			found
		}
		Pat::Ctor(Ctor::Opaque, _) => {
			let rows = default_rows(&rows);
			witnesses(shapes, &rows, tail, tail_types, limit)
				.into_iter()
				.map(|row| prepend(Witness::Wild, row))
				.collect()
		}
		Pat::Ctor(ctor, fields) => {
			let field_types = arity_types(shapes, *ctor, ty);
			let mut q = fields.clone();
			q.extend_from_slice(tail);
			specialised(
				shapes,
				&rows,
				*ctor,
				ty,
				&field_types,
				&q,
				tail_types,
				limit,
			)
		}
		Pat::Wild => {
			let set = shapes.ctor_set(ty);
			let present = present_ctors(&rows);
			let complete = match &set {
				CtorSet::Single | CtorSet::Empty => true,
				CtorSet::Listed(all) => all.iter().all(|c| present.contains(c)),
				CtorSet::Counted { count, .. } => {
					present.len() as u128 == *count
				}
				CtorSet::Unlisted => false,
			};
			if complete {
				let ctors: Vec<Ctor> = match &set {
					CtorSet::Single => vec![Ctor::Single],
					CtorSet::Empty => Vec::new(),
					_ => present.iter().map(|&v| Ctor::Value(v)).collect(),
				};
				let mut found = Vec::new();
				for ctor in ctors {
					let field_types = arity_types(shapes, ctor, ty);
					let mut q = vec![Pat::Wild; field_types.len()];
					q.extend_from_slice(tail);
					let left = limit - found.len();
					found.extend(specialised(
						shapes,
						&rows,
						ctor,
						ty,
						&field_types,
						&q,
						tail_types,
						left,
					));
					if found.len() >= limit {
						break;
					}
				}
				return found;
			}
			let rows = default_rows(&rows);
			let rest = witnesses(shapes, &rows, tail, tail_types, limit);
			if rest.is_empty() {
				return rest;
			}
			// Name the constructors no row has; `_` when no row names any, or
			// when they cannot be listed.
			let missing: Vec<Witness> = if present.is_empty() {
				vec![Witness::Wild]
			} else {
				match &set {
					CtorSet::Listed(all) => all
						.iter()
						.filter(|c| !present.contains(c))
						.map(|&v| value_witness(v, ty))
						.collect(),
					CtorSet::Counted { valid, .. } => (0..)
						.find(|v| valid(*v) && !present.contains(v))
						.map(|v| vec![value_witness(v, ty)])
						.unwrap_or_else(|| vec![Witness::Wild]),
					_ => vec![Witness::Wild],
				}
			};
			let mut found = Vec::new();
			'outer: for row in rest {
				for head in &missing {
					found.push(prepend(head.clone(), row.clone()));
					if found.len() >= limit {
						break 'outer;
					}
				}
			}
			found
		}
	}
}

/// The witnesses of `q` (already specialised: `ctor`'s fields, then the
/// rest) against `rows` specialised by `ctor`, rebuilt with `ctor` at their
/// root.
#[allow(clippy::too_many_arguments)]
fn specialised(
	shapes: &mut dyn Shapes,
	rows: &[Vec<Pat>],
	ctor: Ctor,
	ty: TypeIndex,
	field_types: &[TypeIndex],
	q: &[Pat],
	tail_types: &[TypeIndex],
	limit: usize,
) -> Vec<Vec<Witness>> {
	let arity = field_types.len();
	let rows = specialise(rows, ctor, arity);
	let mut types = field_types.to_vec();
	types.extend_from_slice(tail_types);
	witnesses(shapes, &rows, q, &types, limit)
		.into_iter()
		.map(|mut row| {
			let rest = row.split_off(arity);
			let head = Witness::Ctor {
				ctor,
				ty,
				fields: row,
			};
			prepend(head, rest)
		})
		.collect()
}

/// The types of `ctor`'s fields: `Single`'s are the type's, a value has none.
fn arity_types(
	shapes: &mut dyn Shapes,
	ctor: Ctor,
	ty: TypeIndex,
) -> Vec<TypeIndex> {
	match ctor {
		Ctor::Single => shapes.fields(ty),
		Ctor::Value(_) | Ctor::Opaque => Vec::new(),
	}
}

/// Rows whose first pattern is an `|`, as one row per alternative, until no
/// first pattern is one.
fn expand_or(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
	let mut expanded = Vec::with_capacity(rows.len());
	let mut pending: Vec<Vec<Pat>> = rows.iter().rev().cloned().collect();
	while let Some(row) = pending.pop() {
		match row.first() {
			Some(Pat::Or(alternatives)) => {
				for alternative in alternatives.iter().rev() {
					let mut split = vec![alternative.clone()];
					split.extend_from_slice(&row[1..]);
					pending.push(split);
				}
			}
			_ => expanded.push(row),
		}
	}
	expanded
}

/// The rows that can match `ctor`, with their first pattern replaced by its
/// `arity` sub-patterns. An opaque first pattern may or may not match, so it
/// is dropped: it never covers a known constructor.
fn specialise(rows: &[Vec<Pat>], ctor: Ctor, arity: usize) -> Vec<Vec<Pat>> {
	rows.iter()
		.filter_map(|row| {
			let (head, tail) = row.split_first().unwrap();
			let mut specialised = match head {
				Pat::Wild => vec![Pat::Wild; arity],
				Pat::Ctor(head, fields) if *head == ctor => fields.clone(),
				Pat::Ctor(..) => return None,
				Pat::Or(_) => unreachable!("expanded before"),
			};
			specialised.extend_from_slice(tail);
			Some(specialised)
		})
		.collect()
}

/// The rows headed by a wildcard, without it.
fn default_rows(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
	rows.iter()
		.filter(|row| matches!(row[0], Pat::Wild))
		.map(|row| row[1..].to_vec())
		.collect()
}

/// The values heading the rows, each once, in first-seen order.
fn present_ctors(rows: &[Vec<Pat>]) -> Vec<u64> {
	let mut present = Vec::new();
	for row in rows {
		if let Pat::Ctor(Ctor::Value(value), _) = row[0]
			&& !present.contains(&value)
		{
			present.push(value);
		}
	}
	present
}

fn value_witness(value: u64, ty: TypeIndex) -> Witness {
	Witness::Ctor {
		ctor: Ctor::Value(value),
		ty,
		fields: Vec::new(),
	}
}

fn prepend(head: Witness, mut row: Vec<Witness>) -> Vec<Witness> {
	row.insert(0, head);
	row
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Types as the tests name them, borrowing pre-interned indices as
	/// labels: a pair of `B`s, `B` (two values), an integer with four values,
	/// and one whose values cannot be listed.
	struct TestShapes;

	const PAIR: TypeIndex = TypeIndex::UNIT;
	const B: TypeIndex = TypeIndex::BOOL;
	const NIBBLE: TypeIndex = TypeIndex::U8;
	const OPEN: TypeIndex = TypeIndex::F32;

	impl Shapes for TestShapes {
		fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet {
			match ty {
				PAIR => CtorSet::Single,
				B => CtorSet::Listed(vec![0, 1]),
				NIBBLE => CtorSet::Counted {
					count: 4,
					valid: |_| true,
				},
				_ => CtorSet::Unlisted,
			}
		}

		fn fields(&mut self, ty: TypeIndex) -> Vec<TypeIndex> {
			assert_eq!(ty, PAIR);
			vec![B, B]
		}
	}

	fn value(v: u64) -> Pat {
		Pat::Ctor(Ctor::Value(v), Vec::new())
	}

	fn pair(a: Pat, b: Pat) -> Pat {
		Pat::Ctor(Ctor::Single, vec![a, b])
	}

	fn render(witness: &Witness) -> String {
		match witness {
			Witness::Wild => "_".to_string(),
			Witness::Ctor {
				ctor: Ctor::Value(v),
				..
			} => v.to_string(),
			Witness::Ctor { fields, .. } => {
				let fields: Vec<String> = fields.iter().map(render).collect();
				format!("({})", fields.join(", "))
			}
		}
	}

	/// The witnesses of `_` after `arms`: what the match misses.
	fn missing(arms: Vec<Pat>, ty: TypeIndex) -> Vec<String> {
		let rows: Vec<Vec<Pat>> =
			arms.into_iter().map(|arm| vec![arm]).collect();
		witnesses(&mut TestShapes, &rows, &[Pat::Wild], &[ty], 8)
			.iter()
			.map(|row| render(&row[0]))
			.collect()
	}

	fn useful(arms: Vec<Pat>, q: Pat, ty: TypeIndex) -> bool {
		let rows: Vec<Vec<Pat>> =
			arms.into_iter().map(|arm| vec![arm]).collect();
		!witnesses(&mut TestShapes, &rows, &[q], &[ty], 1).is_empty()
	}

	#[test]
	fn a_listed_set_is_covered_by_its_values() {
		assert!(missing(vec![value(0), value(1)], B).is_empty());
		assert_eq!(missing(vec![value(0)], B), ["1"]);
		assert_eq!(missing(vec![], B), ["_"]);
	}

	#[test]
	fn a_product_is_covered_column_by_column() {
		let arms = vec![pair(value(1), Pat::Wild), pair(Pat::Wild, value(0))];
		assert_eq!(missing(arms, PAIR), ["(0, 1)"]);
		let arms = vec![
			pair(value(1), Pat::Wild),
			pair(Pat::Wild, value(0)),
			pair(value(0), value(1)),
		];
		assert!(missing(arms, PAIR).is_empty());
	}

	#[test]
	fn a_counted_set_needs_every_value_or_a_wildcard() {
		let some = vec![value(0), value(2)];
		assert_eq!(missing(some, NIBBLE), ["1"]);
		let all = (0..4).map(value).collect();
		assert!(missing(all, NIBBLE).is_empty());
	}

	#[test]
	fn an_unlisted_type_needs_a_wildcard() {
		assert_eq!(missing(vec![Pat::Ctor(Ctor::Opaque, vec![])], OPEN), ["_"]);
		assert!(missing(vec![Pat::Wild], OPEN).is_empty());
	}

	#[test]
	fn alternatives_are_rows_of_their_own() {
		let arms = vec![Pat::Or(vec![value(0), value(1)])];
		assert!(missing(arms, B).is_empty());
		// An arm is useful when any alternative is.
		assert!(useful(vec![value(0)], Pat::Or(vec![value(0), value(1)]), B));
		assert!(!useful(
			vec![value(0), value(1)],
			Pat::Or(vec![value(1)]),
			B
		));
	}

	#[test]
	fn an_opaque_constant_covers_nothing_but_is_covered_by_a_wildcard() {
		let opaque = Pat::Ctor(Ctor::Opaque, vec![]);
		assert!(useful(vec![opaque.clone()], value(1), NIBBLE));
		assert!(useful(vec![value(1)], opaque.clone(), NIBBLE));
		assert!(!useful(vec![Pat::Wild], opaque, NIBBLE));
	}
}
