//! Usefulness: which arms of a match match some value that no arm before
//! them does, and which values no arm matches. An arm (or one alternative of
//! an `|`) that matches nothing new is unreachable, and the values no arm
//! matches are the *witnesses* that name what a non-exhaustive match misses.
//!
//! This is the algorithm of Maranget's "Warnings for pattern matching", in the
//! single-pass form rustc's `rustc_pattern_analysis` computes. Patterns are
//! seen as constructors applied to sub-patterns (`Pat`), the arms as the rows
//! of a matrix, and each step looks at the first column only:
//!
//! - *Specialising* by a constructor `c` keeps the rows that can match `c`, and
//!   replaces their first pattern by its sub-patterns (a wildcard by as many
//!   wildcards).
//! - The *default* rows are the ones headed by a wildcard, without it: what is
//!   left to match a value whose constructor no row names.
//!
//! Splitting every column this way until none is left divides the values into
//! regions, one per leaf of the walk. In each, the first row left is the arm
//! that matches those values, and with no row left they are a witness. So one
//! walk over all the arms finds both: the rows first in some leaf
//! (`Analysis::useful`) and the witnesses. A row knows where it came from (its
//! arm, and the alternatives it took, `Origins`), so reachability is read from
//! that list afterwards, for arms and alternatives alike.
//!
//! A match's patterns live in one arena (`Patterns`), built before the
//! algorithm runs and only read by it: a row is a run of ids into it, so
//! specialising rearranges ids and never copies a pattern.
//!
//! The module is pure: what a type's constructors are and what a constructor's
//! fields are is asked of a `Shapes`, which the checker implements.

use super::types::TypeIndex;
use crate::index::index_newtype;

index_newtype!(
	/// A pattern in a match's `Patterns`.
	PatId
);

/// What a pattern matches at its root.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Ctor {
	/// The one constructor of a tuple or a struct, with one field per element
	/// or field.
	Single,
	/// A value of a type with many: an integer (its bits), a `Char` (its code
	/// point), or an enum's variant (its discriminant's bits).
	Value(u64),
	/// A constant compared by its type's `Eq` (a struct's value, a trait's
	/// declaration, one with no value here): it matches some values, never a
	/// known set, so it covers nothing but itself, and only a wildcard covers
	/// it. Two with the same identity are the same test, run on the same
	/// value: once one has failed, the other fails too (trusting `eq` to
	/// answer the same question the same way, as the `Eq` contract says). The
	/// identity is the checker's to assign: what makes two constants the same
	/// is not this module's concern.
	Opaque(u32),
}

/// A pattern, as the algorithm sees it.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Pat {
	/// `_`, a binding, or anything that matches every value.
	Wild,
	/// A constructor and its fields' patterns, one per field.
	Ctor(Ctor, PatList),
	/// Alternatives, each its own row.
	Or(PatList),
}

/// A run of `Patterns::lists`: a constructor's fields or an `|`'s
/// alternatives.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct PatList {
	start: u32,
	len: u32,
}

/// A match's patterns: every pattern of its arms, and every list of them, as
/// columns. The first pattern is the wildcard, which every `_` and binding
/// shares.
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Patterns {
	pats: Vec<Pat>,
	lists: Vec<PatId>,
}

impl Patterns {
	pub(super) const WILD: PatId = PatId(0);

	pub(super) fn new() -> Self {
		Self {
			pats: vec![Pat::Wild],
			lists: Vec::new(),
		}
	}

	/// `ctor` applied to `fields`. The one constructor of a tuple or a struct
	/// with every field a wildcard matches every value, so it is the wildcard
	/// (`Errno(_)`, `(_, _)`, and, built from the inside out, `P(Q(_), _)`):
	/// it then covers what only a wildcard covers, an opaque constant.
	pub(super) fn ctor(&mut self, ctor: Ctor, fields: &[PatId]) -> PatId {
		if ctor == Ctor::Single && fields.iter().all(|&f| f == Self::WILD) {
			return Self::WILD;
		}
		let fields = self.list(fields);
		self.push(Pat::Ctor(ctor, fields))
	}

	pub(super) fn or(&mut self, alternatives: &[PatId]) -> PatId {
		let alternatives = self.list(alternatives);
		self.push(Pat::Or(alternatives))
	}

	fn push(&mut self, pat: Pat) -> PatId {
		self.pats.push(pat);
		PatId::new(self.pats.len() as u32 - 1)
	}

	fn list(&mut self, ids: &[PatId]) -> PatList {
		let start = self.lists.len() as u32;
		self.lists.extend_from_slice(ids);
		PatList {
			start,
			len: ids.len() as u32,
		}
	}

	fn pat(&self, id: PatId) -> Pat {
		self.pats[usize::from(id)]
	}

	fn patterns(&self, list: PatList) -> &[PatId] {
		&self.lists[list.start as usize..(list.start + list.len) as usize]
	}
}

index_newtype!(
	/// A row of a match's matrices, as `Origins` records where it came from.
	RowId
);

/// One alternative of an `|`: the `|` and the alternative's position in it.
/// Not the alternative's own pattern, which may be shared (every `_` is
/// `Patterns::WILD`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Alternative {
	pub(super) or: PatId,
	pub(super) index: u32,
}

impl Alternative {
	/// What alternatives are sorted and searched by.
	fn key(self) -> (u32, u32) {
		(u32::from(self.or), self.index)
	}
}

/// Where each row of a match's matrices came from, as a tree in columns: an
/// arm's own row has no parent, and a row an `|` expanded has the row it was
/// expanded from, and the alternative it took. Specialising keeps a row's
/// origin, so every row derived from it is the same row here.
#[derive(Default)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
struct Origins {
	parent: Vec<Option<RowId>>,
	arm: Vec<u32>,
	alternative: Vec<Option<Alternative>>,
}

impl Origins {
	fn arm(&mut self, arm: u32) -> RowId {
		self.push(None, arm, None)
	}

	fn alternative(
		&mut self,
		parent: RowId,
		alternative: Alternative,
	) -> RowId {
		let arm = self.arm[usize::from(parent)];
		self.push(Some(parent), arm, Some(alternative))
	}

	fn push(
		&mut self,
		parent: Option<RowId>,
		arm: u32,
		alternative: Option<Alternative>,
	) -> RowId {
		self.parent.push(parent);
		self.arm.push(arm);
		self.alternative.push(alternative);
		RowId::new(self.parent.len() as u32 - 1)
	}

	/// The row and every row it was expanded from, up to its arm's.
	fn ancestry(&self, row: RowId) -> impl Iterator<Item = RowId> + '_ {
		std::iter::successors(Some(row), |&row| self.parent[usize::from(row)])
	}
}

/// Rows of patterns, all of `width` columns, in one buffer, reading their
/// patterns from a match's `Patterns`, each with its origin. No row is headed
/// by an `|`: rows are added only by `push_row`, which expands it.
#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
struct Matrix {
	width: usize,
	cells: Vec<PatId>,
	origins: Vec<RowId>,
}

impl Matrix {
	fn new(width: usize) -> Self {
		Self {
			width,
			cells: Vec::new(),
			origins: Vec::new(),
		}
	}

	/// Pushes `row`, from `origin`, as one row per alternative while its head
	/// is an `|`, each recorded as taken from `origin`. Every row is pushed
	/// here, so none is headed by one: specialising never meets an `|`, and no
	/// step has to look for one.
	fn push_row(
		&mut self,
		pats: &Patterns,
		origins: &mut Origins,
		row: &[PatId],
		origin: RowId,
	) {
		match row.split_first() {
			Some((&head, tail)) => {
				self.push_expanded(pats, origins, head, tail, origin);
			}
			None => self.push(row.iter().copied(), origin),
		}
	}

	fn push_expanded(
		&mut self,
		pats: &Patterns,
		origins: &mut Origins,
		head: PatId,
		tail: &[PatId],
		origin: RowId,
	) {
		match pats.pat(head) {
			Pat::Or(alternatives) => {
				for (index, &alternative) in
					pats.patterns(alternatives).iter().enumerate()
				{
					let taken = origins.alternative(
						origin,
						Alternative {
							or: head,
							index: index as u32,
						},
					);
					self.push_expanded(pats, origins, alternative, tail, taken);
				}
			}
			_ => self.push(
				std::iter::once(head).chain(tail.iter().copied()),
				origin,
			),
		}
	}

	fn push(&mut self, row: impl IntoIterator<Item = PatId>, origin: RowId) {
		self.cells.extend(row);
		self.origins.push(origin);
		debug_assert_eq!(self.cells.len(), self.origins.len() * self.width);
	}

	/// Each row with its origin, in order; a row of no columns is an empty
	/// slice.
	fn rows(&self) -> impl Iterator<Item = (&[PatId], RowId)> {
		self.origins.iter().enumerate().map(|(row, &origin)| {
			(
				&self.cells[row * self.width..(row + 1) * self.width],
				origin,
			)
		})
	}

	/// The rows that can match `ctor`, with their first pattern replaced by
	/// its `arity` sub-patterns. An opaque first pattern is kept only for the
	/// same opaque constant: it may or may not match any other constructor,
	/// so it never covers one.
	fn specialise(
		&self,
		pats: &Patterns,
		origins: &mut Origins,
		ctor: Ctor,
		arity: usize,
	) -> Matrix {
		let mut specialised = Matrix::new(self.width - 1 + arity);
		// Each kept row is assembled here, then pushed (and expanded, if its
		// new head is an `|`).
		let mut row_buffer = Vec::with_capacity(specialised.width);
		for (row, origin) in self.rows() {
			let (&head, tail) = row.split_first().unwrap();
			row_buffer.clear();
			match pats.pat(head) {
				Pat::Wild => row_buffer.resize(arity, Patterns::WILD),
				Pat::Ctor(head, fields) if head == ctor => {
					row_buffer.extend_from_slice(pats.patterns(fields));
				}
				Pat::Ctor(..) => continue,
				Pat::Or(_) => {
					unreachable!("no row of a matrix is headed by an `|`")
				}
			}
			row_buffer.extend_from_slice(tail);
			specialised.push_row(pats, origins, &row_buffer, origin);
		}
		specialised
	}

	/// The rows headed by a wildcard, without it.
	fn default_rows(&self, pats: &Patterns, origins: &mut Origins) -> Matrix {
		let mut default = Matrix::new(self.width - 1);
		for (row, origin) in self.rows() {
			if let Pat::Wild = pats.pat(row[0]) {
				default.push_row(pats, origins, &row[1..], origin);
			}
		}
		default
	}

	/// The constructors heading the rows that are not `Single` (values and
	/// opaque constants), each once, in first-seen order.
	fn head_ctors(&self, pats: &Patterns) -> Vec<Ctor> {
		let mut present = Vec::new();
		for (row, _) in self.rows() {
			if let Pat::Ctor(ctor @ (Ctor::Value(_) | Ctor::Opaque(_)), _) =
				pats.pat(row[0])
				&& !present.contains(&ctor)
			{
				present.push(ctor);
			}
		}
		present
	}
}

/// Every constructor of a type.
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum CtorSet {
	/// A tuple, a struct, `()`.
	Single,
	/// A finite set of values, all listed: an enum's variants'.
	Listed(Vec<u64>),
	/// `count` values, in order from `0` up, too many to list: an integer's
	/// (by their bits).
	Counted { count: u128 },
	/// No values at all (`!`): no arm is needed.
	Empty,
	/// Values no pattern can list (floats, pointers, type parameters): only a
	/// wildcard covers them.
	Unlisted,
}

impl CtorSet {
	/// What a column is split into when the rows name every constructor
	/// (`Single`'s one, each value of a listed or counted set), the `present`
	/// values: those constructors. `None` when some are missing, which the
	/// default rows then stand for.
	fn complete(&self, present: &[u64]) -> Option<Vec<Ctor>> {
		let values = || present.iter().map(|&v| Ctor::Value(v)).collect();
		match self {
			Self::Single => Some(vec![Ctor::Single]),
			Self::Empty => Some(Vec::new()),
			Self::Listed(all) if all.iter().all(|c| present.contains(c)) => {
				Some(values())
			}
			Self::Counted { count } if present.len() as u128 == *count => {
				Some(values())
			}
			Self::Listed(_) | Self::Counted { .. } | Self::Unlisted => None,
		}
	}

	/// The constructors of type `ty` that none of the `present` values is,
	/// as witnesses: `_` when no value is present, or when they cannot be
	/// listed.
	fn missing(&self, present: &[u64], ty: TypeIndex) -> Vec<Witness> {
		if present.is_empty() {
			return vec![Witness::Wild];
		}
		match self {
			Self::Listed(all) => all
				.iter()
				.filter(|c| !present.contains(c))
				.map(|&v| Witness::value(v, ty))
				.collect(),
			Self::Counted { .. } => (0..)
				.find(|v| !present.contains(v))
				.map(|v| vec![Witness::value(v, ty)])
				.unwrap_or_else(|| vec![Witness::Wild]),
			_ => vec![Witness::Wild],
		}
	}
}

/// What the algorithm asks of types.
pub(super) trait Shapes {
	fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet;
	/// The types of the fields of `ty`'s `Single` constructor.
	fn fields(&mut self, ty: TypeIndex) -> Vec<TypeIndex>;
}

/// A value no row matches, as a pattern: `Wild` stands for any value.
#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum Witness {
	Wild,
	Ctor {
		ctor: Ctor,
		ty: TypeIndex,
		fields: Vec<Witness>,
	},
}

impl Witness {
	fn value(value: u64, ty: TypeIndex) -> Self {
		Self::Ctor {
			ctor: Ctor::Value(value),
			ty,
			fields: Vec::new(),
		}
	}
}

/// The algorithm over one match's patterns, asking `shapes` about types.
pub(super) struct Usefulness<'a, S: Shapes> {
	shapes: &'a mut S,
	pats: &'a Patterns,
	origins: Origins,
	/// The rows first in some leaf, in the order found, each as often as it
	/// is.
	useful: Vec<RowId>,
}

impl<'a, S: Shapes> Usefulness<'a, S> {
	pub(super) fn new(shapes: &'a mut S, pats: &'a Patterns) -> Self {
		Self {
			shapes,
			pats,
			origins: Origins::default(),
			useful: Vec::new(),
		}
	}

	/// Walks the match whose arms are `arms`, in order, on a value of type
	/// `ty`, and keeps at most `limit` of the values none matches.
	pub(super) fn analyse(
		mut self,
		arms: &[PatId],
		ty: TypeIndex,
		limit: usize,
	) -> Analysis {
		let mut rows = Matrix::new(1);
		for (arm, &pattern) in arms.iter().enumerate() {
			let origin = self.origins.arm(arm as u32);
			rows.push_row(self.pats, &mut self.origins, &[pattern], origin);
		}
		let missing = self
			.walk(&rows, &[ty], limit)
			.into_iter()
			.map(|mut row| row.remove(0))
			.collect();
		Analysis {
			origins: self.origins,
			useful: self.useful,
			arms: arms.len(),
			missing,
		}
	}

	/// Splits `rows`, of columns of `types`, until no column is left,
	/// recording the first row of each leaf with rows in `useful`; returns
	/// the leaves without, as witnesses, at most `limit`. Every branch is
	/// walked whatever the limit, since each may hold a row's only leaf.
	fn walk(
		&mut self,
		rows: &Matrix,
		types: &[TypeIndex],
		limit: usize,
	) -> Vec<Vec<Witness>> {
		let Some((&ty, tail_types)) = types.split_first() else {
			return match rows.origins.first() {
				Some(&first) => {
					self.useful.push(first);
					Vec::new()
				}
				None if limit > 0 => vec![Vec::new()],
				None => Vec::new(),
			};
		};
		let pats = self.pats;
		let set = self.shapes.ctor_set(ty);
		let heads = rows.head_ctors(pats);
		let present: Vec<u64> = heads
			.iter()
			.filter_map(|ctor| match *ctor {
				Ctor::Value(value) => Some(value),
				_ => None,
			})
			.collect();
		// An opaque constant decides only which rows match its own value: a
		// value it misses is one the rows without it miss too, so only
		// usefulness is read from it.
		for &ctor in &heads {
			if let Ctor::Opaque(_) = ctor {
				self.walk_specialised(rows, ctor, ty, tail_types, 0);
			}
		}
		if let Some(ctors) = set.complete(&present) {
			let mut found = Vec::new();
			for ctor in ctors {
				let left = limit - found.len();
				found.extend(
					self.walk_specialised(rows, ctor, ty, tail_types, left),
				);
			}
			return found;
		}
		// Some constructors are named and others are not. The named ones
		// still decide which rows match their values, but their rows include
		// every default row, so what they miss the default rows miss too:
		// the witnesses are the default rows', with a missing constructor.
		for &ctor in &heads {
			if let Ctor::Value(_) = ctor {
				self.walk_specialised(rows, ctor, ty, tail_types, 0);
			}
		}
		let default = rows.default_rows(pats, &mut self.origins);
		let rest = self.walk(&default, tail_types, limit);
		if rest.is_empty() {
			return rest;
		}
		let missing = set.missing(&present, ty);
		let mut found = Vec::new();
		'outer: for row in rest {
			for head in &missing {
				if found.len() >= limit {
					break 'outer;
				}
				found.push(prepend(head.clone(), row.clone()));
			}
		}
		found
	}

	/// `walk` of `rows` specialised by `ctor`, with its witnesses rebuilt with
	/// `ctor` at their root.
	fn walk_specialised(
		&mut self,
		rows: &Matrix,
		ctor: Ctor,
		ty: TypeIndex,
		tail_types: &[TypeIndex],
		limit: usize,
	) -> Vec<Vec<Witness>> {
		let field_types = self.arity_types(ctor, ty);
		let arity = field_types.len();
		let rows = rows.specialise(self.pats, &mut self.origins, ctor, arity);
		let types = [&field_types, tail_types].concat();
		self.walk(&rows, &types, limit)
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

	/// The types of `ctor`'s fields: `Single`'s are the type's, a value has
	/// none.
	fn arity_types(&mut self, ctor: Ctor, ty: TypeIndex) -> Vec<TypeIndex> {
		match ctor {
			Ctor::Single => self.shapes.fields(ty),
			Ctor::Value(_) | Ctor::Opaque(_) => Vec::new(),
		}
	}
}

/// What a walk found: the rows first in some leaf, where each came from, and
/// the values no arm matches.
pub(super) struct Analysis {
	origins: Origins,
	useful: Vec<RowId>,
	arms: usize,
	/// The values no arm matches, as patterns of the matched type.
	pub(super) missing: Vec<Witness>,
}

impl Analysis {
	/// The arms no leaf has first: each matches only values an arm before it
	/// does.
	pub(super) fn unreachable_arms(&self) -> Vec<usize> {
		let reached = self.reached_arms();
		(0..self.arms)
			.filter(|arm| reached.binary_search(&(*arm as u32)).is_err())
			.collect()
	}

	/// The alternatives no leaf has first, in arms that are reachable: each
	/// matches only values the arms and alternatives before it do. An
	/// alternative inside one that is unreachable itself is left to it.
	pub(super) fn unreachable_alternatives(&self) -> Vec<Alternative> {
		let reached_arms = self.reached_arms();
		let mut reached: Vec<Alternative> = self
			.useful
			.iter()
			.flat_map(|&row| self.origins.ancestry(row))
			.filter_map(|row| self.origins.alternative[usize::from(row)])
			.collect();
		reached.sort_unstable_by_key(|alternative| alternative.key());
		reached.dedup();
		let is_unreached = |alternative: Alternative| {
			reached
				.binary_search_by_key(&alternative.key(), |known| known.key())
				.is_err()
		};
		let mut unreachable: Vec<Alternative> = (0..self.origins.parent.len())
			.map(|row| RowId::new(row as u32))
			.filter(|&row| {
				let arm = self.origins.arm[usize::from(row)];
				reached_arms.binary_search(&arm).is_ok()
			})
			.filter_map(|row| {
				let alternative = self.origins.alternative[usize::from(row)]?;
				let outermost = self
					.origins
					.ancestry(row)
					.skip(1)
					.filter_map(|row| {
						self.origins.alternative[usize::from(row)]
					})
					.all(|outer| !is_unreached(outer));
				(is_unreached(alternative) && outermost).then_some(alternative)
			})
			.collect();
		unreachable.sort_unstable_by_key(|alternative| alternative.key());
		unreachable.dedup();
		unreachable
	}

	/// The arms some leaf has first, sorted.
	fn reached_arms(&self) -> Vec<u32> {
		let mut reached: Vec<u32> = self
			.useful
			.iter()
			.map(|&row| self.origins.arm[usize::from(row)])
			.collect();
		reached.sort_unstable();
		reached.dedup();
		reached
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
	const WILD: PatId = Patterns::WILD;

	impl Shapes for TestShapes {
		fn ctor_set(&mut self, ty: TypeIndex) -> CtorSet {
			match ty {
				PAIR => CtorSet::Single,
				B => CtorSet::Listed(vec![0, 1]),
				NIBBLE => CtorSet::Counted { count: 4 },
				_ => CtorSet::Unlisted,
			}
		}

		fn fields(&mut self, ty: TypeIndex) -> Vec<TypeIndex> {
			assert_eq!(ty, PAIR);
			vec![B, B]
		}
	}

	fn value(pats: &mut Patterns, v: u64) -> PatId {
		pats.ctor(Ctor::Value(v), &[])
	}

	fn opaque(pats: &mut Patterns, id: u32) -> PatId {
		pats.ctor(Ctor::Opaque(id), &[])
	}

	fn pair(pats: &mut Patterns, a: PatId, b: PatId) -> PatId {
		pats.ctor(Ctor::Single, &[a, b])
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

	fn analyse(pats: &Patterns, arms: &[PatId], ty: TypeIndex) -> Analysis {
		Usefulness::new(&mut TestShapes, pats).analyse(arms, ty, 8)
	}

	/// The witnesses after `arms`: what the match misses.
	fn missing(pats: &Patterns, arms: &[PatId], ty: TypeIndex) -> Vec<String> {
		analyse(pats, arms, ty).missing.iter().map(render).collect()
	}

	/// Whether `q`, after `arms`, matches anything they do not.
	fn useful(
		pats: &Patterns,
		arms: &[PatId],
		q: PatId,
		ty: TypeIndex,
	) -> bool {
		let all = [arms, &[q]].concat();
		!analyse(pats, &all, ty)
			.unreachable_arms()
			.contains(&arms.len())
	}

	#[test]
	fn a_listed_set_is_covered_by_its_values() {
		let mut p = Patterns::new();
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		assert!(missing(&p, &[zero, one], B).is_empty());
		assert_eq!(missing(&p, &[zero], B), ["1"]);
		assert_eq!(missing(&p, &[], B), ["_"]);
	}

	#[test]
	fn a_product_is_covered_column_by_column() {
		let mut p = Patterns::new();
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		let first = pair(&mut p, one, WILD);
		let second = pair(&mut p, WILD, zero);
		assert_eq!(missing(&p, &[first, second], PAIR), ["(0, 1)"]);
		let third = pair(&mut p, zero, one);
		assert!(missing(&p, &[first, second, third], PAIR).is_empty());
	}

	#[test]
	fn a_counted_set_needs_every_value_or_a_wildcard() {
		let mut p = Patterns::new();
		let all: Vec<PatId> = (0..4).map(|v| value(&mut p, v)).collect();
		assert_eq!(missing(&p, &[all[0], all[2]], NIBBLE), ["1"]);
		assert!(missing(&p, &all, NIBBLE).is_empty());
	}

	#[test]
	fn an_unlisted_type_needs_a_wildcard() {
		let mut p = Patterns::new();
		let constant = opaque(&mut p, 0);
		assert_eq!(missing(&p, &[constant], OPEN), ["_"]);
		assert!(missing(&p, &[WILD], OPEN).is_empty());
	}

	#[test]
	fn alternatives_are_rows_of_their_own() {
		let mut p = Patterns::new();
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		let either = p.or(&[zero, one]);
		assert!(missing(&p, &[either], B).is_empty());
		// An arm is useful when any alternative is.
		assert!(useful(&p, &[zero], either, B));
		let just_one = p.or(&[one]);
		assert!(!useful(&p, &[zero, one], just_one, B));
		// Nested alternatives expand all the way.
		let nested = p.or(&[just_one, zero]);
		assert!(missing(&p, &[nested], B).is_empty());
	}

	#[test]
	fn an_opaque_constant_covers_nothing_but_is_covered_by_a_wildcard() {
		let mut p = Patterns::new();
		let one = value(&mut p, 1);
		let (a, b) = (opaque(&mut p, 0), opaque(&mut p, 1));
		assert!(useful(&p, &[a], one, NIBBLE));
		assert!(useful(&p, &[one], a, NIBBLE));
		assert!(!useful(&p, &[WILD], a, NIBBLE));
		// Opaque constants never complete a type.
		assert_eq!(missing(&p, &[a, b], NIBBLE), ["_"]);
	}

	#[test]
	fn an_opaque_constant_covers_itself_and_no_other() {
		let mut p = Patterns::new();
		let (a, b) = (opaque(&mut p, 0), opaque(&mut p, 1));
		assert!(!useful(&p, &[a], a, OPEN));
		assert!(useful(&p, &[a], b, OPEN));
		// The same identity in another arena slot is the same constant.
		let a_again = opaque(&mut p, 0);
		assert!(!useful(&p, &[a], a_again, OPEN));
		// Inside a product, column by column.
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		let arms = [pair(&mut p, a, zero), pair(&mut p, a, one)];
		let covered = pair(&mut p, a, WILD);
		assert!(!useful(&p, &arms, covered, PAIR));
		let other = pair(&mut p, b, WILD);
		assert!(useful(&p, &arms, other, PAIR));
	}

	#[test]
	fn an_alternative_covered_before_it_is_unreachable() {
		let mut p = Patterns::new();
		let all: Vec<PatId> = (0..4).map(|v| value(&mut p, v)).collect();
		// `0`, `1`, then `3 | 0`: the arm is reachable through `3`.
		let or = p.or(&[all[3], all[0]]);
		let analysis = analyse(&p, &[all[0], all[1], or], NIBBLE);
		assert!(analysis.unreachable_arms().is_empty());
		assert_eq!(
			analysis.unreachable_alternatives(),
			[Alternative { or, index: 1 }]
		);
		// The same alternative twice in one `|`.
		let twice = p.or(&[all[2], all[2]]);
		let analysis = analyse(&p, &[twice], NIBBLE);
		assert_eq!(
			analysis.unreachable_alternatives(),
			[Alternative {
				or: twice,
				index: 1
			}]
		);
	}

	#[test]
	fn an_alternative_useful_under_any_constructor_is_reachable() {
		let mut p = Patterns::new();
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		// `(0, 1)`, `(1, 0)`, then `(_, 0 | 1)`: `0` is new for `(0, 0)`, and
		// `1` for `(1, 1)`.
		let first = pair(&mut p, zero, one);
		let second = pair(&mut p, one, zero);
		let either = p.or(&[zero, one]);
		let third = pair(&mut p, WILD, either);
		let analysis = analyse(&p, &[first, second, third], PAIR);
		assert!(analysis.unreachable_arms().is_empty());
		assert!(analysis.unreachable_alternatives().is_empty());
		// Nested in a constructor: `(_, 1 | 1)` reports the second `1`.
		let ones = p.or(&[one, one]);
		let nested = pair(&mut p, WILD, ones);
		assert_eq!(
			analyse(&p, &[nested], PAIR).unreachable_alternatives(),
			[Alternative { or: ones, index: 1 }]
		);
	}

	#[test]
	fn a_product_of_wildcards_is_a_wildcard() {
		let mut p = Patterns::new();
		let both = pair(&mut p, WILD, WILD);
		assert_eq!(both, WILD);
		let nested = pair(&mut p, both, WILD);
		assert_eq!(nested, WILD);
		// So it covers an opaque constant, as `_` does.
		let constant = opaque(&mut p, 0);
		assert!(!useful(&p, &[nested], constant, PAIR));
	}

	#[test]
	fn an_unreachable_arm_reports_none_of_its_alternatives() {
		let mut p = Patterns::new();
		let (zero, one) = (value(&mut p, 0), value(&mut p, 1));
		let either = p.or(&[zero, one]);
		let analysis = analyse(&p, &[WILD, either], B);
		assert_eq!(analysis.unreachable_arms(), [1]);
		assert!(analysis.unreachable_alternatives().is_empty());
	}
}
