//! Operators: the trait each overloadable operator dispatches through, and the
//! operators the compiler implements natively on primitive scalars.
//!
//! Every operator is checked through its trait, so whether it applies to a
//! type and what it returns are the trait's answer. Only the node built for it
//! differs: on a primitive scalar the operation is the primitive's own
//! (`PrimitiveBinary`/`PrimitiveUnary`, lowered to native instructions and
//! folded by constant evaluation), on any other type it is a call of the
//! impl's or the trait's method. The primitive table below must
//! name exactly the primitive impls the stdlib defines; a test holds the two
//! together.

use super::defs::{
	BindingKey, DefinitionRegistry, FunctionIdx, MemberKind, TraitIdx,
};
use super::types::TypeIndex;
use crate::ast::{BinaryOp, StringInterner, UnaryOp};

/// A primitive scalar type: what builtin operators are defined on.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Scalar {
	U8,
	I8,
	U16,
	I16,
	U32,
	I32,
	U64,
	I64,
	F32,
	F64,
	Bool,
	Char,
}

impl Scalar {
	#[cfg(test)]
	pub(super) const ALL: [Scalar; 12] = [
		Self::U8,
		Self::I8,
		Self::U16,
		Self::I16,
		Self::U32,
		Self::I32,
		Self::U64,
		Self::I64,
		Self::F32,
		Self::F64,
		Self::Bool,
		Self::Char,
	];

	pub(super) fn from_type(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::U8 => Self::U8,
			TypeIndex::I8 => Self::I8,
			TypeIndex::U16 => Self::U16,
			TypeIndex::I16 => Self::I16,
			TypeIndex::U32 => Self::U32,
			TypeIndex::I32 => Self::I32,
			TypeIndex::U64 => Self::U64,
			TypeIndex::I64 => Self::I64,
			TypeIndex::F32 => Self::F32,
			TypeIndex::F64 => Self::F64,
			TypeIndex::BOOL => Self::Bool,
			TypeIndex::CHAR => Self::Char,
			_ => return None,
		})
	}

	pub(super) fn ty(self) -> TypeIndex {
		match self {
			Self::U8 => TypeIndex::U8,
			Self::I8 => TypeIndex::I8,
			Self::U16 => TypeIndex::U16,
			Self::I16 => TypeIndex::I16,
			Self::U32 => TypeIndex::U32,
			Self::I32 => TypeIndex::I32,
			Self::U64 => TypeIndex::U64,
			Self::I64 => TypeIndex::I64,
			Self::F32 => TypeIndex::F32,
			Self::F64 => TypeIndex::F64,
			Self::Bool => TypeIndex::BOOL,
			Self::Char => TypeIndex::CHAR,
		}
	}

	pub(super) fn is_integer(self) -> bool {
		matches!(
			self,
			Self::U8
				| Self::I8 | Self::U16
				| Self::I16 | Self::U32
				| Self::I32 | Self::U64
				| Self::I64
		)
	}

	pub(super) fn is_signed(self) -> bool {
		matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
	}

	pub(super) fn is_float(self) -> bool {
		matches!(self, Self::F32 | Self::F64)
	}

	/// Width in bits of an integer scalar.
	pub(super) fn bits(self) -> u32 {
		match self {
			Self::U8 | Self::I8 => 8,
			Self::U16 | Self::I16 => 16,
			Self::U32 | Self::I32 | Self::F32 | Self::Char => 32,
			Self::U64 | Self::I64 | Self::F64 => 64,
			Self::Bool => 1,
		}
	}
}

/// Whether the compiler implements `op` natively on `ty`, a primitive
/// scalar; `false` for any other type. Mirrors the stdlib's primitive impls of
/// the operator traits exactly (`primitive_operators_match_the_stdlib_impls`);
/// `&&`/`||` are not overloadable and exist only on `bool`.
pub(super) fn is_primitive_binary(op: BinaryOp, ty: TypeIndex) -> bool {
	let Some(scalar) = Scalar::from_type(ty) else {
		return false;
	};
	let numeric = scalar.is_integer() || scalar.is_float();
	match op {
		BinaryOp::Add
		| BinaryOp::Sub
		| BinaryOp::Mul
		| BinaryOp::Div
		| BinaryOp::Rem => numeric,
		BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => {
			scalar.is_integer() || scalar == Scalar::Bool
		}
		BinaryOp::LeftShift | BinaryOp::RightShift => scalar.is_integer(),
		BinaryOp::Eq
		| BinaryOp::NotEq
		| BinaryOp::Less
		| BinaryOp::LessEq
		| BinaryOp::Greater
		| BinaryOp::GreaterEq => true,
		BinaryOp::And | BinaryOp::Or => scalar == Scalar::Bool,
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
		| BinaryOp::RightShiftAssign => false,
	}
}

/// See `is_primitive_binary`.
pub(super) fn is_primitive_unary(op: UnaryOp, ty: TypeIndex) -> bool {
	let Some(scalar) = Scalar::from_type(ty) else {
		return false;
	};
	match op {
		UnaryOp::InvertSign => scalar.is_float() || scalar.is_signed(),
		UnaryOp::BitNot => scalar.is_integer(),
		UnaryOp::Not => scalar == Scalar::Bool,
	}
}

/// Comparisons answer `bool`; every other operator answers its operand type.
pub(super) fn is_comparison(op: BinaryOp) -> bool {
	matches!(
		op,
		BinaryOp::Eq
			| BinaryOp::NotEq
			| BinaryOp::Less
			| BinaryOp::LessEq
			| BinaryOp::Greater
			| BinaryOp::GreaterEq
	)
}

/// The trait an overloadable operator dispatches through and the method it
/// names, as declared by the trait.
#[derive(Clone, Copy)]
pub(super) struct OperatorMethod {
	pub(super) trait_index: TraitIdx,
	pub(super) method: FunctionIdx,
}

/// Every overloadable operator's method, resolved once from the `#[tag]`ged
/// traits phase 1 recorded (`IntrinsicDefs`). A slot is `None` when the stdlib
/// in use does not define the trait (or the method), in which case the
/// operator applies to nothing.
pub(super) struct OperatorTraits {
	add: Option<OperatorMethod>,
	sub: Option<OperatorMethod>,
	mul: Option<OperatorMethod>,
	div: Option<OperatorMethod>,
	rem: Option<OperatorMethod>,
	bitand: Option<OperatorMethod>,
	bitor: Option<OperatorMethod>,
	bitxor: Option<OperatorMethod>,
	shl: Option<OperatorMethod>,
	shr: Option<OperatorMethod>,
	eq: Option<OperatorMethod>,
	ne: Option<OperatorMethod>,
	lt: Option<OperatorMethod>,
	le: Option<OperatorMethod>,
	gt: Option<OperatorMethod>,
	ge: Option<OperatorMethod>,
	neg: Option<OperatorMethod>,
	bitnot: Option<OperatorMethod>,
	not: Option<OperatorMethod>,
}

impl OperatorTraits {
	pub(super) fn new(
		defs: &DefinitionRegistry,
		strings: &StringInterner,
	) -> Self {
		let intrinsics = &defs.intrinsics;
		let method = |trait_index: Option<TraitIdx>, name: &str| {
			let trait_index = trait_index?;
			let key = BindingKey::value(strings.get(name)?);
			match defs.declared_trait_member(trait_index, key)? {
				MemberKind::Method(method) | MemberKind::Function(method) => {
					Some(OperatorMethod {
						trait_index,
						method,
					})
				}
				MemberKind::Constant(_) | MemberKind::AssociatedType(_) => None,
			}
		};
		Self {
			add: method(intrinsics.add, "add"),
			sub: method(intrinsics.sub, "sub"),
			mul: method(intrinsics.mul, "mul"),
			div: method(intrinsics.div, "div"),
			rem: method(intrinsics.rem, "rem"),
			bitand: method(intrinsics.bitand, "bitand"),
			bitor: method(intrinsics.bitor, "bitor"),
			bitxor: method(intrinsics.bitxor, "bitxor"),
			shl: method(intrinsics.shl, "shl"),
			shr: method(intrinsics.shr, "shr"),
			eq: method(intrinsics.partial_eq, "eq"),
			ne: method(intrinsics.partial_eq, "ne"),
			lt: method(intrinsics.partial_ord, "lt"),
			le: method(intrinsics.partial_ord, "le"),
			gt: method(intrinsics.partial_ord, "gt"),
			ge: method(intrinsics.partial_ord, "ge"),
			neg: method(intrinsics.neg, "neg"),
			bitnot: method(intrinsics.bitnot, "bitnot"),
			not: method(intrinsics.not, "not"),
		}
	}

	/// `None` for an operator no trait overloads (`&&`, `||`, assignment) or
	/// whose trait the stdlib does not define.
	pub(super) fn binary(&self, op: BinaryOp) -> Option<OperatorMethod> {
		match op {
			BinaryOp::Add => self.add,
			BinaryOp::Sub => self.sub,
			BinaryOp::Mul => self.mul,
			BinaryOp::Div => self.div,
			BinaryOp::Rem => self.rem,
			BinaryOp::BitAnd => self.bitand,
			BinaryOp::BitOr => self.bitor,
			BinaryOp::BitXor => self.bitxor,
			BinaryOp::LeftShift => self.shl,
			BinaryOp::RightShift => self.shr,
			BinaryOp::Eq => self.eq,
			BinaryOp::NotEq => self.ne,
			BinaryOp::Less => self.lt,
			BinaryOp::LessEq => self.le,
			BinaryOp::Greater => self.gt,
			BinaryOp::GreaterEq => self.ge,
			BinaryOp::And
			| BinaryOp::Or
			| BinaryOp::Assign
			| BinaryOp::AddAssign
			| BinaryOp::SubAssign
			| BinaryOp::MulAssign
			| BinaryOp::DivAssign
			| BinaryOp::RemAssign
			| BinaryOp::BitAndAssign
			| BinaryOp::BitOrAssign
			| BinaryOp::BitXorAssign
			| BinaryOp::LeftShiftAssign
			| BinaryOp::RightShiftAssign => None,
		}
	}

	pub(super) fn unary(&self, op: UnaryOp) -> Option<OperatorMethod> {
		match op {
			UnaryOp::InvertSign => self.neg,
			UnaryOp::BitNot => self.bitnot,
			UnaryOp::Not => self.not,
		}
	}
}
