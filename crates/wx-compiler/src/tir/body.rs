//! Checked expression trees, stored as arenas: one `Body` per definition that
//! has one (a constant's initializer now; function bodies later), with every
//! node addressed by an `ExprIdx` into it.
//!
//! The arena is split by access pattern. `kinds` and `types` are what passes
//! read and what literal coercion rewrites in place; `spans` are only read for
//! diagnostics. A node's children are pushed before it, so every child index is
//! smaller than its parent's and the root is the last node.

use super::defs::{ConstIdx, FunctionIdx};
use super::types::TypeIndex;
use crate::ast::{BinaryOp, UnaryOp};
use crate::diagnostics::TextSpan;
use crate::index::index_newtype;

index_newtype!(ExprIdx);

/// A run of `Body::extra`: the arguments of a call, in order.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ExprRange {
	start: u32,
	len: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ExprKind {
	/// Already reported; whatever reads it stays silent.
	Error,
	/// A form the checker does not cover yet. It has no type, so nothing is
	/// checked against it, and constant evaluation refuses it. It disappears as
	/// the checker grows.
	Unsupported,
	/// A literal's magnitude, as written; `-1` is `Unary` over `Int(1)`.
	Int(u64),
	Float(f64),
	Bool(bool),
	Char(char),
	Const(ConstIdx),
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
}

/// One definition's checked expression tree.
pub(super) struct Body {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
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
}

/// Builds a `Body`. The checker owns one while it walks a definition, and may
/// rewrite a node's kind or type after pushing it (literal coercion).
#[derive(Default)]
pub(super) struct BodyBuilder {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
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

	pub(super) fn push_args(
		&mut self,
		args: impl IntoIterator<Item = ExprIdx>,
	) -> ExprRange {
		let start = u32::try_from(self.extra.len()).unwrap();
		self.extra.extend(args);
		let len = u32::try_from(self.extra.len()).unwrap() - start;
		ExprRange { start, len }
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
			root,
		}
	}

	fn children(&self, kind: ExprKind) -> impl Iterator<Item = ExprIdx> + '_ {
		let (fixed, args): ([Option<ExprIdx>; 2], &[ExprIdx]) = match kind {
			ExprKind::Unary { operand, .. } => ([Some(operand), None], &[]),
			ExprKind::Binary { lhs, rhs, .. } => ([Some(lhs), Some(rhs)], &[]),
			ExprKind::MethodCall { args, .. }
			| ExprKind::GenericMethodCall { args, .. } => (
				[None, None],
				&self.extra
					[args.start as usize..(args.start + args.len) as usize],
			),
			ExprKind::Error
			| ExprKind::Unsupported
			| ExprKind::Int(_)
			| ExprKind::Float(_)
			| ExprKind::Bool(_)
			| ExprKind::Char(_)
			| ExprKind::Const(_) => ([None, None], &[]),
		};
		fixed.into_iter().flatten().chain(args.iter().copied())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn an_expression_node_stays_small() {
		assert!(std::mem::size_of::<ExprKind>() <= 16);
	}
}
