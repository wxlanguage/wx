//! Checked expression trees, stored as arenas: one `Body` per definition that
//! has one (a constant's initializer now; function bodies later), with every
//! node addressed by an `ExprIdx` into it.
//!
//! The arena is split by access pattern. `kinds` and `types` are what passes
//! read and what literal coercion rewrites in place; `spans` are only read for
//! diagnostics. A node's children are pushed before it, so every child index is
//! smaller than its parent's and the root is the last node.

use super::defs::{ConstIdx, FunctionIdx, StructIdx};
use super::types::TypeIndex;
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::TextSpan;
use crate::index::index_newtype;

index_newtype!(ExprIdx);
// The declared position of a parameter: what an argument gives. A struct's
// fields are the parameters of its construction, in declaration order.
index_newtype!(ParamIdx);

/// A run of `Body::extra`: the arguments of a call or a construction, in the
/// order they are written, which is the order they are evaluated in.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ExprRange {
	start: u32,
	len: u32,
}

impl ExprRange {
	pub(super) fn len(self) -> usize {
		self.len as usize
	}
}

/// How the written order of arguments relates to the declared order of what
/// they give.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ArgOrder {
	/// The n-th argument gives the n-th parameter.
	InOrder,
	/// A run of `Body::arg_order` starting at `start` gives the parameter of
	/// each argument, so it is as long as the arguments it belongs to.
	Permuted { start: u32 },
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ExprKind {
	/// Already reported; whatever reads it stays silent.
	Error,
	/// A literal's magnitude, as written; `-1` is `Unary` over `Int(1)`.
	Int(u64),
	Float(f64),
	Bool(bool),
	Char(char),
	Const(ConstIdx),
	/// An enum variant written without a value: the value of the variant
	/// before it, plus one, in the enum's repr.
	NextDiscriminant(ConstIdx),
	/// A builtin operator: the operand is a primitive scalar.
	Unary {
		op: UnaryOp,
		operand: ExprIdx,
	},
	/// A builtin operator: both operands are the same primitive scalar, or
	/// `bool` for `&&`/`||`.
	Binary {
		op: BinaryOp,
		lhs: ExprIdx,
		rhs: ExprIdx,
	},
	/// An operator on a concrete non-primitive type: a call to the selected
	/// impl's method, the receiver first in `args`.
	MethodCall {
		method: FunctionIdx,
		args: ExprRange,
	},
	/// An operator on an abstract type: the trait's declaration of the method,
	/// selected once the receiver is known (monomorphization).
	GenericMethodCall {
		method: FunctionIdx,
		args: ExprRange,
	},
	/// A tuple of its elements, in order: `(a, b)`, `(a,)` or `()`.
	Tuple {
		elements: ExprRange,
	},
	/// A struct built from its fields, written as a call to its name;
	/// `order` says which field each argument gives. A construction
	/// missing a field, which is reported, has fewer arguments than the struct
	/// has fields.
	StructConstructor {
		struct_index: StructIdx,
		args: ExprRange,
		order: ArgOrder,
	},
}

/// One definition's checked expression tree.
pub(super) struct Body {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
	arg_order: Vec<ParamIdx>,
	root: ExprIdx,
}

impl Body {
	pub(super) fn root(&self) -> ExprIdx {
		self.root
	}

	pub(super) fn kind(&self, expr: ExprIdx) -> ExprKind {
		self.kinds[usize::from(expr)]
	}

	pub(super) fn ty(&self, expr: ExprIdx) -> TypeIndex {
		self.types[usize::from(expr)]
	}

	pub(super) fn span(&self, expr: ExprIdx) -> TextSpan {
		self.spans[usize::from(expr)]
	}

	pub(super) fn args(&self, range: ExprRange) -> &[ExprIdx] {
		&self.extra[range.start as usize..(range.start + range.len) as usize]
	}

	/// The parameter the argument at `at`, in written order, gives.
	pub(super) fn declared_index(
		&self,
		order: ArgOrder,
		at: usize,
	) -> ParamIdx {
		match order {
			ArgOrder::InOrder => ParamIdx::new(at as u32),
			ArgOrder::Permuted { start } => self.arg_order[start as usize + at],
		}
	}
}

/// Builds a `Body`. The checker owns one while it walks a definition, and may
/// rewrite a node's kind or type after pushing it (literal coercion).
#[derive(Default)]
pub(super) struct BodyBuilder {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
	arg_order: Vec<ParamIdx>,
}

impl BodyBuilder {
	pub(super) fn push(
		&mut self,
		kind: ExprKind,
		ty: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let index = ExprIdx::new(u32::try_from(self.kinds.len()).unwrap());
		debug_assert!(
			self.children(kind)
				.all(|child| u32::from(child) < u32::from(index)),
			"children are pushed before their parent"
		);
		self.kinds.push(kind);
		self.types.push(ty);
		self.spans.push(span);
		index
	}

	/// The arguments pushed as `range`.
	pub(super) fn args(&self, range: ExprRange) -> &[ExprIdx] {
		&self.extra[range.start as usize..(range.start + range.len) as usize]
	}

	pub(super) fn push_args(
		&mut self,
		args: impl IntoIterator<Item = ExprIdx>,
	) -> ExprRange {
		let start = u32::try_from(self.extra.len()).unwrap();
		self.extra.extend(args);
		let len = u32::try_from(self.extra.len()).unwrap() - start;
		ExprRange { start, len }
	}

	/// Records the field each argument of a call written by name gives, in
	/// the order of the arguments.
	pub(super) fn push_permutation(
		&mut self,
		declared: impl IntoIterator<Item = ParamIdx>,
	) -> ArgOrder {
		let start = u32::try_from(self.arg_order.len()).unwrap();
		self.arg_order.extend(declared);
		ArgOrder::Permuted { start }
	}

	pub(super) fn kind(&self, expr: ExprIdx) -> ExprKind {
		self.kinds[usize::from(expr)]
	}

	pub(super) fn ty(&self, expr: ExprIdx) -> TypeIndex {
		self.types[usize::from(expr)]
	}

	pub(super) fn span(&self, expr: ExprIdx) -> TextSpan {
		self.spans[usize::from(expr)]
	}

	pub(super) fn set_kind(&mut self, expr: ExprIdx, kind: ExprKind) {
		self.kinds[usize::from(expr)] = kind;
	}

	pub(super) fn set_ty(&mut self, expr: ExprIdx, ty: TypeIndex) {
		self.types[usize::from(expr)] = ty;
	}

	pub(super) fn finish(self, root: ExprIdx) -> Body {
		debug_assert_eq!(usize::from(root) + 1, self.kinds.len());
		Body {
			kinds: self.kinds,
			types: self.types,
			spans: self.spans,
			extra: self.extra,
			arg_order: self.arg_order,
			root,
		}
	}

	fn children(&self, kind: ExprKind) -> impl Iterator<Item = ExprIdx> + '_ {
		let (fixed, args): ([Option<ExprIdx>; 2], &[ExprIdx]) = match kind {
			ExprKind::Unary { operand, .. } => ([Some(operand), None], &[]),
			ExprKind::Binary { lhs, rhs, .. } => ([Some(lhs), Some(rhs)], &[]),
			ExprKind::MethodCall { args, .. }
			| ExprKind::GenericMethodCall { args, .. }
			| ExprKind::StructConstructor { args, .. }
			| ExprKind::Tuple { elements: args } => (
				[None, None],
				&self.extra
					[args.start as usize..(args.start + args.len) as usize],
			),
			ExprKind::Error
			| ExprKind::Int(_)
			| ExprKind::Float(_)
			| ExprKind::Bool(_)
			| ExprKind::Char(_)
			| ExprKind::Const(_)
			| ExprKind::NextDiscriminant(_) => ([None, None], &[]),
		};
		fixed.into_iter().flatten().chain(args.iter().copied())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn an_expression_node_stays_small() {
		assert!(std::mem::size_of::<ExprKind>() <= 24);
	}
}
