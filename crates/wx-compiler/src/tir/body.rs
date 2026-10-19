//! Checked expression trees, stored as arenas: one `Body` per definition that
//! has one (a constant's initializer, a function's body, a global's
//! initializer), with every node addressed by an `ExprIdx` into it.
//!
//! The arena is split by access pattern. `kinds` and `types` are what passes
//! read and what literal coercion rewrites in place; `spans` are only read for
//! diagnostics. A node's children are pushed before it, so every child index is
//! smaller than its parent's and the root is the last node.
//!
//! Beside the expressions, a body keeps its lexical structure: the block
//! scopes it is made of, the locals each declares and the labels written on
//! them. A scope is allocated when the checker enters its block, before any
//! node inside it, so a `break` can name the scope it leaves. Places, the
//! locations in linear memory an expression reads, writes or takes the address
//! of, have an arena of their own, pushed children first like expressions.

use string_interner::symbol::SymbolU32;

use super::defs::{ConstIdx, FieldIdx, FunctionIdx, GlobalIdx, StructIdx};
use super::types::TypeIndex;
use crate::ast::{BinaryOp, Spanned, UnaryOp};
use crate::diagnostics::TextSpan;
use crate::index::index_newtype;

index_newtype!(ExprIdx);
// The declared position of a parameter: what an argument gives. A struct's
// fields are the parameters of its construction, in declaration order.
index_newtype!(ParamIdx);
index_newtype!(ScopeIdx);
index_newtype!(LocalIdx);
index_newtype!(LabelIdx);
index_newtype!(PlaceIdx);

impl ScopeIdx {
	/// Every body's outermost scope: a function's parameters are declared in
	/// it, and `return` leaves it.
	pub(super) const ROOT: ScopeIdx = ScopeIdx(0);
}

/// The definition a body belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum BodyOwner {
	Const(ConstIdx),
	Function(FunctionIdx),
	Global(GlobalIdx),
}

/// A run of `Body::extra`: the arguments of a call or a construction, in the
/// order they are written, which is the order they are evaluated in; or the
/// statements of a block.
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
	/// A literal's magnitude, as written; `-1` is `PrimitiveUnary` over
	/// `Int(1)`.
	Int(u64),
	Float(f64),
	Bool(bool),
	Char(char),
	Const(ConstIdx),
	/// An enum variant written without a value: the value of the variant
	/// before it, plus one, in the enum's repr.
	NextDiscriminant(ConstIdx),
	/// A local's value.
	Local(LocalIdx),
	/// A global's handle, of its own nominal type (`Type::Global`).
	Global(GlobalIdx),
	/// A function as a value, of its own zero-sized type (`Type::Function`,
	/// which carries the type arguments).
	Function(FunctionIdx),
	// Operators and compound assignment. A name says what defines the
	// operation: `Primitive`, the operator of a primitive scalar (it holds the
	// `op`); `Impl`, the method of the impl selected for a concrete type;
	// `Trait`, the trait's declaration of the method, for an abstract type,
	// whose impl is selected at monomorphization (both hold the `method`).
	// It then says where the result goes: `Assign`, a local or a field of
	// one; `Store`, a place in linear memory; neither, it is a value.
	/// `op operand` on a primitive scalar.
	PrimitiveUnary {
		op: UnaryOp,
		operand: ExprIdx,
	},
	/// `lhs op rhs` where both are the same primitive scalar, or `bool` for
	/// `&&`/`||`.
	PrimitiveBinary {
		op: BinaryOp,
		lhs: ExprIdx,
		rhs: ExprIdx,
	},
	/// An operator on a concrete type: a call of the selected impl's method,
	/// the receiver first in `args`.
	ImplMethodCall {
		method: FunctionIdx,
		args: ExprRange,
	},
	/// An operator on an abstract type: a call of the trait's declaration of
	/// the method, the receiver first in `args`.
	TraitMethodCall {
		method: FunctionIdx,
		args: ExprRange,
	},
	/// A call of `callee`, a `Function` node whose type carries the type
	/// arguments the call was checked with.
	Call {
		callee: ExprIdx,
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
	/// `value as T`; the node's type is `T`.
	Cast {
		value: ExprIdx,
	},
	/// `value.field` on a value that is not in linear memory (a local, a
	/// global, a call's result). The field is its declared index.
	FieldAccess {
		object: ExprIdx,
		field: FieldIdx,
	},
	/// Reads the value stored at a place in linear memory: `p.*`, `p.*.x`.
	Load(PlaceIdx),
	/// `place.&`: the address of a place, a shared pointer into its memory.
	AddressOf(PlaceIdx),
	/// `{ statements; result }`, owning `scope`. Its type is its result's, or
	/// `()` without one; `!` when a statement diverges and nothing else gives
	/// it a value. A labelled block's `break`s give it a value too.
	Block {
		scope: ScopeIdx,
		statements: ExprRange,
		result: Option<ExprIdx>,
	},
	/// `local name = value`. Typed `()`, or `!` when the value diverges.
	LocalDeclaration {
		local: LocalIdx,
		value: ExprIdx,
	},
	IfElse {
		condition: ExprIdx,
		then_block: ExprIdx,
		else_block: Option<ExprIdx>,
	},
	/// `loop { statements }`, owning `scope`. Its type comes from the
	/// `break`s that leave it; with none, it never ends and is `!`.
	Loop {
		scope: ScopeIdx,
		statements: ExprRange,
	},
	/// Leaves `scope`, a loop or a labelled block, giving it `value`.
	Break {
		scope: ScopeIdx,
		value: Option<ExprIdx>,
	},
	/// Starts the next iteration of `scope`, a loop.
	Continue {
		scope: ScopeIdx,
	},
	Return {
		value: Option<ExprIdx>,
	},
	/// `_ = value`: the value is evaluated and dropped.
	Drop {
		value: ExprIdx,
	},
	/// `target = value`, where `target` is a `Local` or a `FieldAccess`
	/// rooted in one: a location that is not in linear memory. A global is
	/// never one: it is written through `GlobalMut::set`.
	Assign {
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `place = value` for a place in linear memory. Its own node, apart from
	/// `Assign`, because a place is an address computed once and written
	/// through, not an expression that is evaluated.
	Store {
		place: PlaceIdx,
		value: ExprIdx,
	},
	/// `target op= value` on a primitive scalar (`op` is `Add`, not
	/// `AddAssign`): `target = target op value`, with `target` evaluated once.
	/// `target` is one of `Assign`'s.
	PrimitiveCompoundAssign {
		op: BinaryOp,
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `target op= value` on a concrete type, through the selected impl's
	/// method.
	ImplCompoundAssign {
		method: FunctionIdx,
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `target op= value` on an abstract type, through the trait's
	/// declaration of the method.
	TraitCompoundAssign {
		method: FunctionIdx,
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `place op= value` on a primitive scalar, for a place in linear memory:
	/// its address is computed once and used for both the read and the write.
	PrimitiveCompoundStore {
		op: BinaryOp,
		place: PlaceIdx,
		value: ExprIdx,
	},
	/// `place op= value` on a concrete type, through the selected impl's
	/// method.
	ImplCompoundStore {
		method: FunctionIdx,
		place: PlaceIdx,
		value: ExprIdx,
	},
	/// `place op= value` on an abstract type, through the trait's
	/// declaration of the method.
	TraitCompoundStore {
		method: FunctionIdx,
		place: PlaceIdx,
		value: ExprIdx,
	},
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ScopeKind {
	/// The body itself: a function's block, or a constant's or global's
	/// initializer.
	Root,
	/// A block, an `if`/`else` branch.
	Block,
	/// A loop's block, which `continue` restarts.
	Loop,
}

/// One lexical block.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Scope {
	pub(super) kind: ScopeKind,
	/// `None` only for the root.
	pub(super) parent: Option<ScopeIdx>,
	/// `outer: loop { .. }`. Both branches of a labelled `if` share one.
	pub(super) label: Option<LabelIdx>,
	pub(super) span: TextSpan,
}

/// A label written on a block, a loop or an `if`.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Label {
	pub(super) name: Spanned<SymbolU32>,
}

/// A function's parameter, or a name a `local` declares.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Local {
	pub(super) name: Spanned<SymbolU32>,
	pub(super) ty: TypeIndex,
	pub(super) mut_span: Option<TextSpan>,
	/// The block it is declared in; it is visible from its declaration to the
	/// end of that block.
	pub(super) scope: ScopeIdx,
}

/// A location in linear memory. Every place is reached through a pointer, so
/// the memory it is in and whether it may be written are known when it is
/// built, from that pointer's type.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Place {
	pub(super) kind: PlaceKind,
	/// The type of the value stored there.
	pub(super) ty: TypeIndex,
	/// The `Type::Memory` it is in.
	pub(super) memory: TypeIndex,
	/// Reached through an exclusive pointer (`*T`), so it may be written.
	pub(super) mutable: bool,
	pub(super) span: TextSpan,
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum PlaceKind {
	/// `pointer.*`, the only way into linear memory.
	Deref { pointer: ExprIdx },
	/// `place.field`; in the same memory as `object`, and as writable. The
	/// field is its declared index.
	Field { object: PlaceIdx, field: FieldIdx },
}

/// One definition's checked expression tree.
pub(super) struct Body {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
	arg_order: Vec<ParamIdx>,
	scopes: Vec<Scope>,
	labels: Vec<Label>,
	locals: Vec<Local>,
	places: Vec<Place>,
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

	pub(super) fn scope(&self, scope: ScopeIdx) -> &Scope {
		&self.scopes[usize::from(scope)]
	}

	pub(super) fn label(&self, label: LabelIdx) -> &Label {
		&self.labels[usize::from(label)]
	}

	pub(super) fn local(&self, local: LocalIdx) -> &Local {
		&self.locals[usize::from(local)]
	}

	/// Every local, in declaration order (`LocalIdx` order).
	pub(super) fn locals(&self) -> &[Local] {
		&self.locals
	}

	pub(super) fn place(&self, place: PlaceIdx) -> &Place {
		&self.places[usize::from(place)]
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
	scopes: Vec<Scope>,
	labels: Vec<Label>,
	locals: Vec<Local>,
	places: Vec<Place>,
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

	pub(super) fn push_scope(&mut self, scope: Scope) -> ScopeIdx {
		debug_assert_eq!(self.scopes.is_empty(), scope.parent.is_none());
		let index = ScopeIdx::new(u32::try_from(self.scopes.len()).unwrap());
		self.scopes.push(scope);
		index
	}

	pub(super) fn push_label(&mut self, label: Label) -> LabelIdx {
		let index = LabelIdx::new(u32::try_from(self.labels.len()).unwrap());
		self.labels.push(label);
		index
	}

	pub(super) fn push_local(&mut self, local: Local) -> LocalIdx {
		let index = LocalIdx::new(u32::try_from(self.locals.len()).unwrap());
		self.locals.push(local);
		index
	}

	pub(super) fn push_place(&mut self, place: Place) -> PlaceIdx {
		let index = PlaceIdx::new(u32::try_from(self.places.len()).unwrap());
		self.places.push(place);
		index
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

	pub(super) fn scope(&self, scope: ScopeIdx) -> &Scope {
		&self.scopes[usize::from(scope)]
	}

	pub(super) fn label(&self, label: LabelIdx) -> &Label {
		&self.labels[usize::from(label)]
	}

	pub(super) fn local(&self, local: LocalIdx) -> &Local {
		&self.locals[usize::from(local)]
	}

	pub(super) fn place(&self, place: PlaceIdx) -> &Place {
		&self.places[usize::from(place)]
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
			scopes: self.scopes,
			labels: self.labels,
			locals: self.locals,
			places: self.places,
			root,
		}
	}

	fn children(&self, kind: ExprKind) -> impl Iterator<Item = ExprIdx> + '_ {
		let (fixed, args): ([Option<ExprIdx>; 3], &[ExprIdx]) = match kind {
			ExprKind::PrimitiveUnary { operand, .. } => {
				([Some(operand), None, None], &[])
			}
			ExprKind::PrimitiveBinary { lhs, rhs, .. }
			| ExprKind::Assign {
				target: lhs,
				value: rhs,
			}
			| ExprKind::PrimitiveCompoundAssign {
				target: lhs,
				value: rhs,
				..
			}
			| ExprKind::ImplCompoundAssign {
				target: lhs,
				value: rhs,
				..
			}
			| ExprKind::TraitCompoundAssign {
				target: lhs,
				value: rhs,
				..
			} => ([Some(lhs), Some(rhs), None], &[]),
			ExprKind::FieldAccess { object: value, .. }
			| ExprKind::Cast { value }
			| ExprKind::Drop { value }
			| ExprKind::LocalDeclaration { value, .. }
			| ExprKind::Store { value, .. }
			| ExprKind::PrimitiveCompoundStore { value, .. }
			| ExprKind::ImplCompoundStore { value, .. }
			| ExprKind::TraitCompoundStore { value, .. } => {
				([Some(value), None, None], &[])
			}
			ExprKind::IfElse {
				condition,
				then_block,
				else_block,
			} => ([Some(condition), Some(then_block), else_block], &[]),
			ExprKind::Break { value, .. } | ExprKind::Return { value } => {
				([value, None, None], &[])
			}
			ExprKind::Call { callee, args } => (
				[Some(callee), None, None],
				&self.extra
					[args.start as usize..(args.start + args.len) as usize],
			),
			ExprKind::Block {
				statements, result, ..
			} => (
				[result, None, None],
				&self.extra[statements.start as usize
					..(statements.start + statements.len) as usize],
			),
			ExprKind::ImplMethodCall { args, .. }
			| ExprKind::TraitMethodCall { args, .. }
			| ExprKind::StructConstructor { args, .. }
			| ExprKind::Tuple { elements: args }
			| ExprKind::Loop {
				statements: args, ..
			} => (
				[None, None, None],
				&self.extra
					[args.start as usize..(args.start + args.len) as usize],
			),
			ExprKind::Error
			| ExprKind::Int(_)
			| ExprKind::Float(_)
			| ExprKind::Bool(_)
			| ExprKind::Char(_)
			| ExprKind::Const(_)
			| ExprKind::NextDiscriminant(_)
			| ExprKind::Local(_)
			| ExprKind::Global(_)
			| ExprKind::Function(_)
			| ExprKind::Load(_)
			| ExprKind::AddressOf(_)
			| ExprKind::Continue { .. } => ([None, None, None], &[]),
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
