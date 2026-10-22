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
//!
//! Patterns, what a `local` or a match arm takes apart, binds and tests, have
//! one more, shared by both, pushed children first too. A pattern is typed
//! and resolved: the mode it was written in is gone, and destructuring has
//! one child per element or field of its type, in declaration order.

use string_interner::symbol::SymbolU32;

use super::defs::{ConstIdx, FieldIdx, FunctionIdx, GlobalIdx, StructIdx};
use super::types::{TypeIndex, TypeList};
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
index_newtype!(PatIdx);

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

/// A constant's checked initializer, and how far along it is.
///
/// A body is built on demand (`ensure_const_body`), and building it may read
/// another constant's value — a pattern that names it — which may build
/// *this* constant's body in turn. The `Building` state is what stops that
/// from repeating: a body that is already being built is not built again.
pub(super) enum ConstBody {
	/// Not built yet.
	NotBuilt,
	/// Being built now. A read of this constant's value finds none: its
	/// value cannot be known until its body is built, and its body cannot be
	/// built while it is being built.
	Building,
	/// Built.
	Built(Body),
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

/// A run of `Body::pat_lists`: the children of a tuple, struct or `|`
/// pattern.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct PatternRange {
	start: u32,
	len: u32,
}

/// A run of `Body::arms`: a match's arms, in written order.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct ArmRange {
	start: u32,
	len: u32,
}

/// One arm of a match. Its bindings are declared in `scope`, which holds
/// `body`.
#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Arm {
	pub(super) scope: ScopeIdx,
	pub(super) pattern: PatIdx,
	pub(super) body: ExprIdx,
}

#[derive(Clone, Copy)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum PatternKind {
	// Structure: always matches, and takes the value apart.
	/// `_`, an element or field `..` covers, or a field a named pattern
	/// leaves out.
	Wildcard,
	Bind(LocalIdx),
	/// One child per element of the tuple's type.
	Tuple(PatternRange),
	/// One child per field, in declaration order. The type arguments are the
	/// pattern's type's.
	Struct {
		struct_index: StructIdx,
		fields: PatternRange,
	},

	// Tests: match only some values, so only a match arm holds them.
	/// The value's bits in the pattern's type: `-1` as an `i8` is `0xFF`.
	Int(u64),
	Bool(bool),
	Char(char),
	/// A known constant: a variant, a free one, or an impl's, with its flat
	/// type arguments as `ExprKind::Const` holds them.
	Constant {
		constant: ConstIdx,
		type_args: TypeList,
	},
	/// A trait's declaration of a constant; `type_args` is `[Self]`.
	AbstractConstant {
		constant: ConstIdx,
		type_args: TypeList,
	},
	/// Alternatives, which bind the same names: the same name in two of
	/// them is one local.
	Or(PatternRange),

	/// Already reported; whatever reads it stays silent, and exhaustiveness
	/// counts it as `_`.
	Error,
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
	/// A string literal's contents, unescaped. Its type is a shared byte
	/// slice or byte array its context gives (`Type::String` until then).
	String(SymbolU32),
	/// A known constant's value: a free one, a variant, or an impl's (an
	/// inherent impl's, or the one a concrete trait impl defines), with its
	/// flat type arguments, the impl's; empty when it has none.
	Const {
		constant: ConstIdx,
		type_args: TypeList,
	},
	/// A trait's declaration of a constant, whose impl is selected once
	/// `Self` is known; `type_args` is `[Self]`.
	AbstractConst {
		constant: ConstIdx,
		type_args: TypeList,
	},
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
	// Operators, calls and compound assignment. What defines the operation:
	// a primitive scalar's operator (`Primitive*`, holding the `op`); a known
	// function (`Call`, `ConcreteCompound*`); or a trait's declaration, whose
	// impl is selected at monomorphization (`AbstractCall`,
	// `AbstractCompound*`). A compound assignment's name then says where the
	// result goes: `Assign`, a local or a field of one; `Store`, a place in
	// linear memory. Every function is held with its type arguments, flat: an
	// impl's arguments and then the function's own, or `Self` and then the
	// declaration's own for a trait's.
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
	/// A direct call of a known function: a free function, `Type::f(..)`,
	/// `x.m(..)`, or the impl method an operator on a concrete type selects.
	/// A method's receiver is the first of `args`.
	Call {
		function: FunctionIdx,
		type_args: TypeList,
		args: ExprRange,
	},
	/// A call of a trait's declaration, whose impl is selected once `Self`
	/// is known: for an abstract receiver, or a concrete one whose impl
	/// inherits the trait's default. A method's receiver is the first of
	/// `args`.
	AbstractCall {
		method: FunctionIdx,
		type_args: TypeList,
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
	/// `local pattern = value`. Typed `()`, or `!` when the value diverges.
	/// The pattern always matches: it holds no tests.
	LocalDeclaration {
		pattern: PatIdx,
		value: ExprIdx,
	},
	/// `match scrutinee { arms }`: the first arm whose pattern matches runs.
	/// Its type is the arms' bodies', as an `if`'s is its branches'.
	Match {
		scrutinee: ExprIdx,
		arms: ArmRange,
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
	ConcreteCompoundAssign {
		method: FunctionIdx,
		type_args: TypeList,
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `target op= value` on an abstract type, through the trait's
	/// declaration of the method.
	AbstractCompoundAssign {
		method: FunctionIdx,
		type_args: TypeList,
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
	ConcreteCompoundStore {
		method: FunctionIdx,
		type_args: TypeList,
		place: PlaceIdx,
		value: ExprIdx,
	},
	/// `place op= value` on an abstract type, through the trait's
	/// declaration of the method.
	AbstractCompoundStore {
		method: FunctionIdx,
		type_args: TypeList,
		place: PlaceIdx,
		value: ExprIdx,
	},
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum ScopeKind {
	/// A block, an `if`/`else` branch, a match arm (holding its bindings),
	/// or the body itself (the root scope, the one without a parent).
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
	/// The local each parameter binds, in order; `None` for an unnamed
	/// parameter, which binds nothing. Empty for an initializer.
	params: Vec<Option<LocalIdx>>,
	places: Vec<Place>,
	pat_kinds: Vec<PatternKind>,
	pat_types: Vec<TypeIndex>,
	pat_spans: Vec<TextSpan>,
	pat_lists: Vec<PatIdx>,
	arms: Vec<Arm>,
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

	/// The local each parameter binds, `None` for an unnamed one.
	pub(super) fn params(&self) -> &[Option<LocalIdx>] {
		&self.params
	}

	pub(super) fn place(&self, place: PlaceIdx) -> &Place {
		&self.places[usize::from(place)]
	}

	pub(super) fn pattern(&self, pattern: PatIdx) -> PatternKind {
		self.pat_kinds[usize::from(pattern)]
	}

	pub(super) fn pattern_ty(&self, pattern: PatIdx) -> TypeIndex {
		self.pat_types[usize::from(pattern)]
	}

	pub(super) fn pattern_span(&self, pattern: PatIdx) -> TextSpan {
		self.pat_spans[usize::from(pattern)]
	}

	pub(super) fn patterns(&self, range: PatternRange) -> &[PatIdx] {
		&self.pat_lists
			[range.start as usize..(range.start + range.len) as usize]
	}

	pub(super) fn arms(&self, range: ArmRange) -> &[Arm] {
		&self.arms[range.start as usize..(range.start + range.len) as usize]
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
	params: Vec<Option<LocalIdx>>,
	places: Vec<Place>,
	pat_kinds: Vec<PatternKind>,
	pat_types: Vec<TypeIndex>,
	pat_spans: Vec<TextSpan>,
	pat_lists: Vec<PatIdx>,
	arms: Vec<Arm>,
}

impl BodyBuilder {
	pub(super) fn push(
		&mut self,
		kind: ExprKind,
		ty: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let index = ExprIdx::new(u32::try_from(self.kinds.len()).unwrap());
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

	/// Records the local the next parameter binds, if it has a name.
	pub(super) fn push_param(&mut self, local: Option<LocalIdx>) {
		self.params.push(local);
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

	pub(super) fn push_pattern(
		&mut self,
		kind: PatternKind,
		ty: TypeIndex,
		span: TextSpan,
	) -> PatIdx {
		let index = PatIdx::new(u32::try_from(self.pat_kinds.len()).unwrap());
		self.pat_kinds.push(kind);
		self.pat_types.push(ty);
		self.pat_spans.push(span);
		index
	}

	pub(super) fn push_patterns(
		&mut self,
		patterns: impl IntoIterator<Item = PatIdx>,
	) -> PatternRange {
		let start = u32::try_from(self.pat_lists.len()).unwrap();
		self.pat_lists.extend(patterns);
		let len = u32::try_from(self.pat_lists.len()).unwrap() - start;
		PatternRange { start, len }
	}

	pub(super) fn push_arms(
		&mut self,
		arms: impl IntoIterator<Item = Arm>,
	) -> ArmRange {
		let start = u32::try_from(self.arms.len()).unwrap();
		self.arms.extend(arms);
		let len = u32::try_from(self.arms.len()).unwrap() - start;
		ArmRange { start, len }
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

	pub(super) fn pattern(&self, pattern: PatIdx) -> PatternKind {
		self.pat_kinds[usize::from(pattern)]
	}

	pub(super) fn pattern_ty(&self, pattern: PatIdx) -> TypeIndex {
		self.pat_types[usize::from(pattern)]
	}

	pub(super) fn pattern_span(&self, pattern: PatIdx) -> TextSpan {
		self.pat_spans[usize::from(pattern)]
	}

	pub(super) fn patterns(&self, range: PatternRange) -> &[PatIdx] {
		&self.pat_lists
			[range.start as usize..(range.start + range.len) as usize]
	}

	pub(super) fn arms(&self, range: ArmRange) -> &[Arm] {
		&self.arms[range.start as usize..(range.start + range.len) as usize]
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
			params: self.params,
			places: self.places,
			pat_kinds: self.pat_kinds,
			pat_types: self.pat_types,
			pat_spans: self.pat_spans,
			pat_lists: self.pat_lists,
			arms: self.arms,
			root,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn an_expression_node_stays_small() {
		assert!(std::mem::size_of::<ExprKind>() <= 24);
	}

	#[test]
	fn a_pattern_node_stays_small() {
		assert!(std::mem::size_of::<PatternKind>() <= 16);
	}
}
