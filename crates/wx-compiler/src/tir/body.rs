//! Checked expression trees, stored as arenas: one `Body` per definition that
//! has one (a constant's initializer, a function's body, a global's
//! initializer), with every node addressed by an `ExprIdx` into it.
//!
//! The arena is split by access pattern. `kinds` and `types` are what passes
//! read and what literal coercion rewrites in place; `spans` are only read for
//! diagnostics. A node's children are pushed before it, so every child index is
//! smaller than its parent's and the root is the last node.
//!
//! Beside the expressions, a body keeps its lexical structure, the block
//! scopes it is made of and the locals each declares, and its control flow
//! structure, the loops and `block`s a jump can target, with their labels.
//! Each is allocated when the checker enters it, before any node inside it,
//! so a `break` can name the target it leaves. Places, the
//! locations in linear memory an expression reads, writes or takes the address
//! of, have an arena of their own, pushed children first like expressions.
//!
//! Patterns, what a `local` or a match arm takes apart, binds and tests, have
//! one more, shared by both, pushed children first too. A pattern is typed
//! and resolved: the mode it was written in is gone, and destructuring has
//! one child per element or field of its type, in declaration order.

use string_interner::symbol::SymbolU32;

use super::decls::{
	ConstIdx, FieldIdx, FieldOwner, FunctionIdx, GlobalIdx, ImportIdx,
	MemoryIdx, StructIdx,
};
use super::numbers::DecimalFloat;
use super::obligations::TypeObligation;
use super::signatures::Semantics;
use super::types::{GenericArgs, TypeIndex};
use crate::ast::{self, AST, BinaryOp, ExprId, Expression, Spanned, UnaryOp};
use crate::diagnostics::{TextOffset, TextSpan};
use crate::index::index_newtype;
use crate::symbols::Keyword;

index_newtype!(BodyIdx);
index_newtype!(ExprIdx);
// The declared position of a parameter: what an argument gives. A struct's
// fields are the parameters of its construction, in declaration order.
index_newtype!(ParamIdx);
index_newtype!(ScopeIdx);
index_newtype!(LocalIdx);
index_newtype!(TargetIdx);
index_newtype!(PlaceIdx);
index_newtype!(PatIdx);

impl ScopeIdx {
	/// Every body's outermost scope: a function's parameters are declared in
	/// it, and `return` leaves it.
	pub(super) const ROOT: ScopeIdx = ScopeIdx(0);
}

/// The definition a body belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum BodyOwner {
	Const(ConstIdx),
	Function(FunctionIdx),
	Global(GlobalIdx),
}

/// What implements a function, indexed by `FunctionIdx` in `Semantics`.
/// This is independent of signature-query readiness. A declaration may be a
/// trait requirement or an ordinary bodiless function; its source definition
/// retains that distinction.
#[derive(Clone, Copy)]
pub(super) enum FunctionImplementation {
	/// Its checked block, in `Semantics::bodies`.
	Defined(BodyIdx),
	Imported(ImportIdx),
	/// A package function parameter: whoever instantiates its package
	/// supplies it (for core, the compiler, when lowering).
	Parameter,
	Declaration,
}

impl FunctionImplementation {
	pub(super) fn body(self) -> Option<BodyIdx> {
		match self {
			Self::Defined(body) => Some(body),
			Self::Imported(_) | Self::Parameter | Self::Declaration => None,
		}
	}
}

/// A constant's checked initializer. Every one is built before anything
/// evaluates (`Semantics::build_constant_bodies`), so evaluation never
/// reads a `NotBuilt` one.
#[derive(Clone, Copy)]
pub(super) enum ConstBody {
	/// Not built yet.
	NotBuilt,
	/// Built, in `Semantics::bodies`.
	Built(BodyIdx),
	/// It has none: a required trait constant.
	Missing,
}

/// What a body requires of one of its own expressions, which needs a
/// constant's value to decide: the counterpart of `TypeObligation`, whose
/// subject is a type and which the solver decides. Building a body never reads
/// a value, so it records these beside the body; a function's or a global's are
/// decided as the body is finished, a constant's once every constant it reads
/// is checked (`Semantics::check_constant_bodies`).
#[derive(Clone, Copy)]
pub(super) enum ExprObligation {
	/// `expr`'s type is `expected`; one of them holds a constant not
	/// evaluated yet, as rustc's `ConstEquate`.
	Equal { expr: ExprIdx, expected: TypeIndex },
	/// A string or array literal `expr` of length `length` (a `Value`, or a
	/// `Const` for a repeat's count) is as long as `target`, an array.
	StaticLength {
		expr: ExprIdx,
		target: TypeIndex,
		length: TypeIndex,
	},
	/// A `match`'s exhaustiveness and unreachable arms: a pattern compares
	/// with a constant's value.
	Match(ExprIdx),
	/// An untyped constant `expr` (`const X: const_int`) was given the type
	/// `target`: its value is representable as it, as a literal's would be.
	Representable { expr: ExprIdx, target: TypeIndex },
}

/// What building a body left undecided, beside the body: a function's or a
/// global's are decided as the body is finished, a constant's are kept
/// (`Semantics::const_obligations`) until it is checked.
#[derive(Default)]
pub(super) struct Obligations {
	/// What lowering the body's written types required.
	pub(super) types: Vec<TypeObligation>,
	pub(super) exprs: Vec<ExprObligation>,
}

impl Obligations {
	pub(super) fn is_empty(&self) -> bool {
		self.types.is_empty() && self.exprs.is_empty()
	}
}

/// A run of `Body::extra`: the arguments of a call or a construction, in the
/// order they are written, which is the order they are evaluated in; or the
/// statements of a block.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
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
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct PatternRange {
	start: u32,
	len: u32,
}

/// A run of `Body::locals`: the locals one scope declares.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct LocalRange {
	start: u32,
	len: u32,
}

/// A run of `Body::arms`: a match's arms, in written order.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct ArmRange {
	start: u32,
	len: u32,
}

/// One arm of a match.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Arm {
	pub(super) pattern: PatIdx,
	pub(super) body: ExprIdx,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum PatternKind {
	// Structure: always matches, and takes the value apart.
	/// `_`, an element or field `..` covers, or a field a named pattern
	/// leaves out.
	Wildcard,
	Bind(LocalIdx),
	/// One child per element of the tuple's type.
	Tuple(PatternRange),
	/// Its fields as one value, of the owner's field tuple (a lone field's
	/// own type): a tuple of one child per field in declaration order, or any
	/// pattern of that type (`P(p)`, `P(_)`). A struct's type arguments are
	/// the pattern's type's. An enum's fields are its repr (`Ordering(n)`),
	/// and hold no test: the variants are its values, so its repr matches
	/// whichever it is.
	Fields {
		owner: FieldOwner,
		fields: PatIdx,
	},

	// Tests: match only some values, so only a match arm holds them.
	/// The value's bits in the pattern's type: `-1` as an `i8` is `0xFF`.
	Int(u64),
	Char(char),
	/// A known constant: a variant, a free one, or an impl's, with its flat
	/// type arguments as `ExprKind::Const` holds them.
	Constant {
		constant: ConstIdx,
		type_args: GenericArgs,
	},
	/// A trait's declaration of a constant; `type_args` is `[Self]`.
	AbstractConstant {
		constant: ConstIdx,
		type_args: GenericArgs,
	},
	/// Alternatives, which bind the same names: the same name in two of
	/// them is one local.
	Or(PatternRange),

	/// Already reported. Its type can retain the known subject type; the
	/// kind, not TypeIndex::ERROR, marks failure. Exhaustiveness skips a match
	/// containing one rather than treating it as a valid wildcard.
	Error,
}

/// How the written order of a tuple's elements relates to the positions they
/// give.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum ElementOrder {
	/// The n-th element gives the n-th position.
	InOrder,
	/// A run of `Body::arg_order` starting at `start` gives the position of
	/// each element, so it is as long as the elements it belongs to.
	Permuted { start: u32 },
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum ExprKind {
	/// Already reported; whatever reads it stays silent.
	Error,
	/// A literal's magnitude, as written; `-1` is `PrimitiveUnary` over
	/// `Int(1)`.
	Int(u64),
	/// Exact decimal value. Its checked type determines the precision used
	/// when evaluation or lowering converts it.
	Float(DecimalFloat),
	Char(char),
	/// A string literal's contents, unescaped. Its type is the byte array of
	/// its length (`[u8; 5]`), data in no memory until its context places it
	/// (a shared pointer to it or to the slice of its bytes).
	String(SymbolU32),
	/// An array literal `[a, b, c]`. Its type is the array of its elements and
	/// its length (`[const_int; 3]`), data in no memory until its context
	/// places it, and each element has that type's element type.
	Array {
		elements: ExprRange,
	},
	/// A repeat `[value; count]`, typed as an array literal is, its length
	/// the count; `count` is an integer literal or a constant, or `None` for
	/// `_`, the length of the array its context gives.
	ArrayRepeat {
		value: ExprIdx,
		count: Option<ExprIdx>,
	},
	/// A known constant's value: a free one, a variant, or an impl's (an
	/// inherent impl's, or the one a concrete trait impl defines), with its
	/// flat type arguments, the impl's; empty when it has none.
	Const {
		constant: ConstIdx,
		type_args: GenericArgs,
	},
	/// A trait's declaration of a constant, whose impl is selected once
	/// `Self` is known; `type_args` is `[Self]`.
	AbstractConst {
		constant: ConstIdx,
		type_args: GenericArgs,
	},
	/// An enum variant written without a value: the value of the variant
	/// before it, plus one, in the enum's repr.
	NextDiscriminant(ConstIdx),
	/// A local's value.
	Local(LocalIdx),
	/// A global's handle, of its own nominal type (`Type::Global`).
	Global(GlobalIdx),
	/// A memory's handle, of its own nominal type (`Type::Memory`): the
	/// receiver of `Memory`'s methods (`heap.grow(1)`).
	Memory(
		#[cfg_attr(
			not(test),
			expect(
				dead_code,
				reason = "the type carries it for lowering; the test printer reads it"
			)
		)]
		MemoryIdx,
	),
	/// A function as a value, of its own zero-sized type (`Type::Function`),
	/// with its type arguments, flat as a call's.
	#[cfg_attr(
		not(test),
		expect(
			dead_code,
			reason = "the type carries it for lowering; the test printer reads it"
		)
	)]
	Function {
		function: FunctionIdx,
		type_args: GenericArgs,
	},
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
	/// `lhs op rhs` where both are the same primitive scalar, enum or
	/// pointer, or `Bool` for `&&`/`||`.
	PrimitiveBinary {
		op: BinaryOp,
		lhs: ExprIdx,
		rhs: ExprIdx,
	},
	/// A direct call of a known function: a free function, `Type::f(..)`,
	/// or `Type::m(x, ..)`. `args` is the value of its parameters as one, as
	/// a parameter list forms its type: `()` for none, the argument itself
	/// for one, a `Tuple` for several, or one value written for all of them
	/// (`f(p)`).
	Call {
		function: FunctionIdx,
		type_args: GenericArgs,
		args: ExprIdx,
	},
	/// A call of a trait's declaration, whose impl is selected once `Self`
	/// is known: for an abstract receiver, or a concrete one whose impl
	/// inherits the trait's default. `args` as for `Call`.
	AbstractCall {
		method: FunctionIdx,
		type_args: GenericArgs,
		args: ExprIdx,
	},
	/// `receiver.m(..)` of a known function: an impl method, the impl method
	/// an operator on a concrete type selects, or `Call::call` of a value's
	/// impl. The receiver gives the first parameter and is evaluated first;
	/// `args` is the value of the parameters after it, as for `Call`.
	MethodCall {
		function: FunctionIdx,
		type_args: GenericArgs,
		receiver: ExprIdx,
		args: ExprIdx,
	},
	/// `receiver.m(..)` of a trait's declaration, as `AbstractCall` is to
	/// `Call`: an abstract receiver's method or operator, a default an impl
	/// inherits, or `Call::call` of a function item or an abstract `F: Call`.
	AbstractMethodCall {
		method: FunctionIdx,
		type_args: GenericArgs,
		receiver: ExprIdx,
		args: ExprIdx,
	},
	/// A call through a function reference, `f(a, b)` with `f: func(A) ->
	/// R`, by position only, evaluated after the callee. `args` is its value
	/// of `A`, as for `Call`.
	CallRef {
		callee: ExprIdx,
		args: ExprIdx,
	},
	/// A tuple of its elements: `(a, b)` or `()`. `elements` are in
	/// evaluation order and `order` says which position each gives: in order
	/// as written, permuted for the arguments of a call by name.
	Tuple {
		elements: ExprRange,
		order: ElementOrder,
	},
	/// A struct built from its fields, written as a call to its name;
	/// `fields` is their value as one, as `args` is a call's.
	StructConstructor {
		struct_index: StructIdx,
		fields: ExprIdx,
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
	/// `loop (a = x, b = y) { body }`, owning `scope`, which declares the
	/// parameters, in order. `entry` is the first state, their initial
	/// values as one, built outside the loop; `body` is a `Block` whose
	/// result is the next state. A loop without parameters has the state
	/// `()`. Its type comes from the `break`s that leave it; with none, it
	/// never ends and is `!`.
	Loop {
		scope: ScopeIdx,
		entry: Option<ExprIdx>,
		body: ExprIdx,
	},
	/// Leaves `target`, a loop or a `block`, giving it `value`.
	Break {
		target: TargetIdx,
		value: Option<ExprIdx>,
	},
	/// Starts the next iteration of `target`, a loop, with `value` as its
	/// state (`()` without one).
	Continue {
		target: TargetIdx,
		value: Option<ExprIdx>,
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
		type_args: GenericArgs,
		target: ExprIdx,
		value: ExprIdx,
	},
	/// `target op= value` on an abstract type, through the trait's
	/// declaration of the method.
	AbstractCompoundAssign {
		method: FunctionIdx,
		type_args: GenericArgs,
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
		type_args: GenericArgs,
		place: PlaceIdx,
		value: ExprIdx,
	},
	/// `place op= value` on an abstract type, through the trait's
	/// declaration of the method.
	AbstractCompoundStore {
		method: FunctionIdx,
		type_args: GenericArgs,
		place: PlaceIdx,
		value: ExprIdx,
	},
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum ScopeKind {
	/// The locals of the scopes around it are in reach.
	Ordinary,
	/// A string or array literal's elements, or a repeat's value:
	/// constant expressions, so the locals of the scopes around it are out
	/// of reach. A name still finds them, so a local shadows an item here as
	/// anywhere, and using one is an error (E2108).
	Static,
}

/// One lexical scope: braces (the body, whose root scope declares the
/// parameters, a block, a branch, a match arm from the end of its pattern),
/// a loop's parameters from its block's start, or the rest of a block after
/// a `local` statement, from the statement's end. Each `local` opens one
/// inside the one before, so a later local of the same name shadows by
/// nesting, and the statement's own value, built before it opens, sees the
/// locals before it.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Scope {
	pub(super) kind: ScopeKind,
	/// `None` only for the root.
	pub(super) parent: Option<ScopeIdx>,
	/// Where what it declares is in scope: the offsets after its start, up
	/// to its end.
	pub(super) span: TextSpan,
	/// The locals it declares, one run: the parameters, one pattern's
	/// bindings, or none.
	locals: LocalRange,
}

/// What a jump target is: a `break` may leave either, a `continue`
/// restarts only a loop.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum TargetKind {
	Block,
	Loop,
}

impl TargetKind {
	/// The keyword it is written with.
	pub fn keyword(self) -> Keyword {
		match self {
			TargetKind::Block => Keyword::Block,
			TargetKind::Loop => Keyword::Loop,
		}
	}
}

/// A loop or a `block`: what a `break` leaves or a `continue` restarts.
/// Targets nest by control flow, as scopes nest by visibility. What its node
/// records, its kind, its scope and where its keyword is written, is read
/// from the node (`Body::target_kind` and the rest).
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct JumpTarget {
	/// `loop :outer { .. }` or `block :outer { .. }`.
	pub label: Option<Spanned<SymbolU32>>,
	/// The target it is written in.
	pub parent: Option<TargetIdx>,
	/// Its `Loop` or `Block` node.
	pub(super) construct: ExprIdx,
}

/// A function's parameter, or a name a `local` declares.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub struct Local {
	pub name: Spanned<SymbolU32>,
	pub ty: TypeIndex,
	pub mut_span: Option<TextSpan>,
}

/// A location in linear memory. Every place is reached through a pointer, so
/// the memory it is in and whether it may be written are known when it is
/// built, from that pointer's type.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
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
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum PlaceKind {
	/// `pointer.*`, the only way into linear memory.
	Deref { pointer: ExprIdx },
	/// `place.field`; in the same memory as `object`, and as writable. The
	/// field is its declared index.
	Field { object: PlaceIdx, field: FieldIdx },
	/// `place[index]`, an element of the slice or array `object`; in its
	/// memory, and as writable. The index is the memory's `Size`, checked
	/// against the length when it is read.
	Element { object: PlaceIdx, index: ExprIdx },
}

/// What an expression written in source was checked as: a value, or a
/// place in linear memory when it names one and its use keeps it a place
/// (the left of `=`, the operand of `.&`, the object of `.field`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub enum Operand {
	Place(PlaceIdx),
	Value(ExprIdx),
}

/// A call as checking built it: the selected function and type arguments,
/// a function reference, or a construction. A function can name a trait
/// declaration whose implementation is selected when instantiated. Operands
/// belong to the queried body; type arguments index the existing arena.
pub enum Call {
	Function {
		function: FunctionIdx,
		type_args: GenericArgs,
		receiver: Option<Operand>,
		arguments: Operand,
	},
	Reference {
		callee: Operand,
		arguments: Operand,
	},
	Constructor {
		structure: StructIdx,
		fields: Operand,
	},
}

impl Semantics {
	/// Inspect a checked call without resolving its callee again or
	/// interpreting its packed arguments as a written parameter list.
	pub fn call_of(&self, owner: BodyOwner, value: ExprIdx) -> Option<Call> {
		let body = self.owner_body(owner)?;
		Some(match body.kind(value) {
			ExprKind::Call {
				function,
				type_args,
				args,
			}
			| ExprKind::AbstractCall {
				method: function,
				type_args,
				args,
			} => Call::Function {
				function,
				type_args,
				receiver: None,
				arguments: Operand::Value(args),
			},
			ExprKind::MethodCall {
				function,
				type_args,
				receiver,
				args,
			}
			| ExprKind::AbstractMethodCall {
				method: function,
				type_args,
				receiver,
				args,
			} => Call::Function {
				function,
				type_args,
				receiver: Some(Operand::Value(receiver)),
				arguments: Operand::Value(args),
			},
			ExprKind::CallRef { callee, args } => Call::Reference {
				callee: Operand::Value(callee),
				arguments: Operand::Value(args),
			},
			ExprKind::StructConstructor {
				struct_index,
				fields,
			} => Call::Constructor {
				structure: struct_index,
				fields: Operand::Value(fields),
			},
			_ => return None,
		})
	}
}

/// One definition's checked expression tree.
#[derive(Default)]
pub struct Body {
	kinds: Vec<ExprKind>,
	types: Vec<TypeIndex>,
	spans: Vec<TextSpan>,
	extra: Vec<ExprIdx>,
	arg_order: Vec<ParamIdx>,
	scopes: Vec<Scope>,
	targets: Vec<JumpTarget>,
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
	/// The string and array literals, in arena order (an inner one before the one
	/// holding it): the static data lowering evaluates.
	statics: Vec<ExprIdx>,
}

impl Body {
	/// The last node pushed: every child comes before its parent.
	pub(super) fn root(&self) -> ExprIdx {
		ExprIdx::new(u32::try_from(self.kinds.len() - 1).unwrap())
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

	/// The position the element at `at`, in written order, gives.
	pub(super) fn declared_index(
		&self,
		order: ElementOrder,
		at: usize,
	) -> ParamIdx {
		match order {
			ElementOrder::InOrder => ParamIdx::new(at as u32),
			ElementOrder::Permuted { start } => {
				self.arg_order[start as usize + at]
			}
		}
	}

	pub(super) fn scope(&self, scope: ScopeIdx) -> &Scope {
		&self.scopes[usize::from(scope)]
	}

	/// The locals `scope` declares, in order.
	pub fn scope_locals(
		&self,
		scope: ScopeIdx,
	) -> impl ExactSizeIterator<Item = LocalIdx> + use<> {
		let LocalRange { start, len } = self.scope(scope).locals;
		(start..start + len).map(LocalIdx::new)
	}

	/// How many scopes there are; every `ScopeIdx` is below it.
	pub(super) fn scope_count(&self) -> usize {
		self.scopes.len()
	}

	pub fn target(&self, target: TargetIdx) -> &JumpTarget {
		&self.targets[usize::from(target)]
	}

	pub fn local(&self, local: LocalIdx) -> &Local {
		&self.locals[usize::from(local)]
	}

	/// Every local, in declaration order (`LocalIdx` order).
	pub fn locals(&self) -> &[Local] {
		&self.locals
	}

	/// The innermost scope covering `offset`, if `offset` is in the body. A
	/// scope is pushed after the one holding it, and siblings do not
	/// overlap, so it is the last one covering `offset`.
	fn scope_at(&self, offset: TextOffset) -> Option<ScopeIdx> {
		self.scopes
			.iter()
			.rposition(|scope| {
				scope.span.start < offset && offset < scope.span.end
			})
			.map(|index| ScopeIdx::new(index as u32))
	}

	/// The scopes a name written at `offset` is looked up in, innermost
	/// first, each with the locals it declares.
	fn scopes_from(
		&self,
		offset: TextOffset,
	) -> impl Iterator<Item = (Scope, impl Iterator<Item = LocalIdx>)> + '_ {
		std::iter::successors(self.scope_at(offset), |&at| {
			self.scope(at).parent
		})
		.map(|at| {
			let scope = *self.scope(at);
			let LocalRange { start, len } = scope.locals;
			(scope, (start..start + len).map(LocalIdx::new))
		})
	}

	/// The locals a name written at `offset` can use: for each name, the
	/// one its lookup finds there (`BodyBuilder::lookup_local`), innermost
	/// scope first. Inside a `Static` scope (a literal's elements) the
	/// locals of the scopes around it are out of reach, since using one is
	/// an error (E2108), so they are left out. Empty when `offset` is not
	/// in the body.
	pub fn locals_at(&self, offset: TextOffset) -> Vec<LocalIdx> {
		let mut found: Vec<LocalIdx> = Vec::new();
		for (scope, locals) in self.scopes_from(offset) {
			for local in locals {
				let name = self.local(local).name.inner;
				if !found
					.iter()
					.any(|&kept| self.local(kept).name.inner == name)
				{
					found.push(local);
				}
			}
			if scope.kind == ScopeKind::Static {
				break;
			}
		}
		found
	}

	/// The local `name`, written at `offset`, refers to, as the checker's
	/// lookup finds it: the nearest one declared, past static data too,
	/// where using it is an error (E2108) but it still means that local and
	/// hides an item of its name.
	pub fn local_named_at(
		&self,
		offset: TextOffset,
		name: SymbolU32,
	) -> Option<LocalIdx> {
		self.scopes_from(offset)
			.flat_map(|(_, locals)| locals)
			.find(|&local| self.local(local).name.inner == name)
	}

	/// The labelled targets a `break` or `continue` written at `offset` can
	/// name: for each label, the one its lookup finds there
	/// (`BodyBuilder::jump_target`), innermost first.
	pub fn labels_at(&self, offset: TextOffset) -> Vec<TargetIdx> {
		let innermost = (0..self.targets.len()).rposition(|at| {
			let span = self
				.scope(self.target_scope(TargetIdx::new(at as u32)))
				.span;
			span.start < offset && offset < span.end
		});
		let mut found: Vec<TargetIdx> = Vec::new();
		let chain = std::iter::successors(
			innermost.map(|at| TargetIdx::new(at as u32)),
			|&at| self.target(at).parent,
		);
		for target in chain {
			let Some(label) = self.target(target).label else {
				continue;
			};
			if !found.iter().any(|&kept| {
				self.target(kept).label.unwrap().inner == label.inner
			}) {
				found.push(target);
			}
		}
		found
	}

	/// The type of the value leaving `target` gives: what its `break`s and,
	/// for a `block`, its result give.
	pub fn target_type(&self, target: TargetIdx) -> TypeIndex {
		self.ty(self.target(target).construct)
	}

	pub fn target_kind(&self, target: TargetIdx) -> TargetKind {
		self.target_node(target).0
	}

	/// The scope `target` owns: a loop's parameters, or a `block`'s braces.
	/// A jump gives its value to it.
	pub fn target_scope(&self, target: TargetIdx) -> ScopeIdx {
		self.target_node(target).1
	}

	/// The `loop` or `block` keyword `target` is written with, where its node
	/// starts.
	pub fn target_keyword_span(&self, target: TargetIdx) -> TextSpan {
		let start = self.span(self.target(target).construct).start;
		self.target_kind(target).keyword().span_at(start)
	}

	fn target_node(&self, target: TargetIdx) -> (TargetKind, ScopeIdx) {
		match self.kind(self.target(target).construct) {
			ExprKind::Loop { scope, .. } => (TargetKind::Loop, scope),
			ExprKind::Block { scope, .. } => (TargetKind::Block, scope),
			_ => unreachable!("a target's node is a loop or a block"),
		}
	}

	/// Every loop and `block`, in `TargetIdx` order.
	pub fn targets(&self) -> &[JumpTarget] {
		&self.targets
	}

	/// The local each parameter binds, `None` for an unnamed one.
	pub fn params(&self) -> &[Option<LocalIdx>] {
		&self.params
	}

	/// What the expression `expr` of `ast`, in this body, was checked as.
	/// A tuple of one is checked as its element and an ascription as its
	/// value, neither adding a node, so they are looked through to the node
	/// that was built: `(o)` and `(o: T)` are what `o` was checked as, and
	/// `(5: u8)` is the literal, which coercion made a `u8` in place.
	pub fn operand_of(&self, ast: &AST, expr: ExprId) -> Option<Operand> {
		let mut expr = expr;
		loop {
			expr = match ast.expr(expr) {
				Expression::Tuple { elements } if elements.len() == 1 => {
					ast.list(elements)[0]
				}
				Expression::Ascription { value, .. } => value,
				_ => break,
			};
		}
		self.operand_with_span(ast.expr_span(expr))
	}

	/// The type assigned to a written pattern in this body, including known
	/// subject types retained on failed patterns. This does not imply validity.
	pub fn pattern_type_of(
		&self,
		ast: &AST,
		pattern: ast::PatId,
	) -> Option<TypeIndex> {
		Some(self.pattern_ty(self.pattern_of(ast, pattern)?))
	}

	/// Exact-span lookup, like `operand_of`. Transparent single-element tuples
	/// have no checked node. Synthetic field tuples and omitted-field wildcards
	/// can share a destructure's span; the enclosing written node is built last.
	fn pattern_of(&self, ast: &AST, mut pattern: ast::PatId) -> Option<PatIdx> {
		while let ast::Pattern::Destructure(ast::Destructure::Tuple {
			elements,
		}) = ast.pattern(pattern)
		{
			let [ast::PatternElement::Pattern(child)] = *ast.list(elements)
			else {
				break;
			};
			pattern = child;
		}
		let span = ast.pattern_span(pattern);
		self.pat_spans
			.iter()
			.rposition(|&found| found == span)
			.map(|at| PatIdx::new(at as u32))
	}

	/// The checked subject of a match expression, independently of its
	/// result type and whether it has any arms.
	pub fn match_scrutinee(&self, expr: ExprIdx) -> Option<ExprIdx> {
		match self.kind(expr) {
			ExprKind::Match { scrutinee, .. } => Some(scrutinee),
			_ => None,
		}
	}

	/// The loop the `continue` written as `expr` of `ast` restarts, as it
	/// was checked. `None` for one with no target, which was checked as an
	/// error.
	pub fn continue_target(
		&self,
		ast: &AST,
		expr: ExprId,
	) -> Option<TargetIdx> {
		let Operand::Value(at) = self.operand_with_span(ast.expr_span(expr))?
		else {
			return None;
		};
		match self.kind(at) {
			ExprKind::Continue { target, .. } => Some(target),
			_ => None,
		}
	}

	/// What the expression written at exactly `span` was checked as: the
	/// first expression pushed with that span, else the last place.
	///
	/// An expression is preferred because a place may share its span with
	/// one: `p.field` goes through the pointer `p` with a `Deref` place at
	/// `p`'s span, and `p` is what was written. Among expressions the first
	/// is the one written, as a child is pushed before its parent and what
	/// the checker adds around a value (`receiver.*.&` for a method's shared
	/// receiver) reuses its span. A place is the answer only where no value
	/// was made: a place a field access keeps (`p.inner` in `p.inner.x`,
	/// `p.*` in `p.*.x`). Among places the last is the outermost, which is
	/// what was written.
	fn operand_with_span(&self, span: TextSpan) -> Option<Operand> {
		if let Some(at) = self.spans.iter().position(|&at| at == span) {
			return Some(Operand::Value(ExprIdx::new(at as u32)));
		}
		self.places
			.iter()
			.rposition(|place| place.span == span)
			.map(|at| Operand::Place(PlaceIdx::new(at as u32)))
	}

	/// The type of the value `operand` is, or is the location of.
	pub fn operand_ty(&self, operand: Operand) -> TypeIndex {
		match operand {
			Operand::Place(place) => self.place(place).ty,
			Operand::Value(value) => self.ty(value),
		}
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

	pub(super) fn statics(&self) -> &[ExprIdx] {
		&self.statics
	}
}

impl Body {
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

	pub(super) fn push_args(
		&mut self,
		args: impl IntoIterator<Item = ExprIdx>,
	) -> ExprRange {
		let start = u32::try_from(self.extra.len()).unwrap();
		self.extra.extend(args);
		let len = u32::try_from(self.extra.len()).unwrap() - start;
		ExprRange { start, len }
	}

	/// Records the position each element of a tuple gives, in written order:
	/// the arguments of a call by name.
	pub(super) fn push_permutation(
		&mut self,
		declared: impl IntoIterator<Item = ParamIdx>,
	) -> ElementOrder {
		let start = u32::try_from(self.arg_order.len()).unwrap();
		self.arg_order.extend(declared);
		ElementOrder::Permuted { start }
	}

	pub(super) fn push_scope(
		&mut self,
		kind: ScopeKind,
		parent: Option<ScopeIdx>,
		span: TextSpan,
	) -> ScopeIdx {
		debug_assert_eq!(self.scopes.is_empty(), parent.is_none());
		let index = ScopeIdx::new(u32::try_from(self.scopes.len()).unwrap());
		self.scopes.push(Scope {
			kind,
			parent,
			span,
			locals: LocalRange {
				start: u32::try_from(self.locals.len()).unwrap(),
				len: 0,
			},
		});
		index
	}

	/// Gives the body its jump targets, in `TargetIdx` order. A target is
	/// complete only once its node is built, after the jumps inside it that
	/// name it, so the checker gives them all when the body is.
	pub(super) fn set_targets(&mut self, targets: Vec<JumpTarget>) {
		debug_assert!(self.targets.is_empty());
		self.targets = targets;
	}

	/// Records the local the next parameter binds, if it has a name.
	pub(super) fn push_param(&mut self, local: Option<LocalIdx>) {
		self.params.push(local);
	}

	/// Declares `local` in `scope`. A scope's locals are one run, so it
	/// must be the last scope that declared any.
	pub(super) fn push_local(
		&mut self,
		scope: ScopeIdx,
		local: Local,
	) -> LocalIdx {
		let index = LocalIdx::new(u32::try_from(self.locals.len()).unwrap());
		let run = &mut self.scopes[usize::from(scope)].locals;
		debug_assert_eq!(
			run.start + run.len,
			u32::from(index),
			"a scope's locals are declared together"
		);
		run.len += 1;
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

	pub(super) fn set_kind(&mut self, expr: ExprIdx, kind: ExprKind) {
		self.kinds[usize::from(expr)] = kind;
	}

	/// Records a literal as static data (`Body::statics`).
	pub(super) fn push_static(&mut self, expr: ExprIdx) {
		self.statics.push(expr);
	}

	pub(super) fn set_ty(&mut self, expr: ExprIdx, ty: TypeIndex) {
		self.types[usize::from(expr)] = ty;
	}
}

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::*;
	use crate::diagnostics::{DiagnosticCode, SourceSpan};
	use crate::symbols::{Keyword, StringInterner};
	use crate::testing::DiagnosticView;
	use crate::tir::decls::{FunctionIdx, Scope};
	use crate::tir::resolutions::{Reference, Site};
	use crate::tir::signatures::Semantics;
	use crate::tir::signatures::tests::source_graph;
	use crate::vfs::{self, FileId};

	/// A checked source, read through its bodies.
	struct Case<'s> {
		source: &'s str,
		file: FileId,
		graph: vfs::CompilationUnit,
		strings: StringInterner,
		sema: Semantics,
	}

	impl<'s> Case<'s> {
		fn new(source: &'s str) -> Self {
			let mut strings = Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			Self::checked(source, graph, strings)
		}

		/// A source the parser reports and recovers from.
		fn recovered(source: &'s str) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let root = builder
				.load_package(
					vfs::AbsolutePath::new("/main.wx"),
					&vfs::VirtualFileSource::from_relative(
						std::collections::HashMap::from([(
							"main.wx".to_string(),
							source.to_string(),
						)]),
					),
				)
				.unwrap();
			let graph = builder.build(root);
			Self::checked(source, graph, strings)
		}

		fn checked(
			source: &'s str,
			graph: vfs::CompilationUnit,
			mut strings: StringInterner,
		) -> Self {
			let sema = crate::tir::check(&graph, &mut strings);
			let file = sema
				.decls
				.namespaces
				.file_id(Scope::Package(sema.decls.root_package).into());
			Self {
				source,
				file,
				graph,
				strings,
				sema,
			}
		}

		/// The body of the function named `name`.
		fn body(&self, name: &str) -> &Body {
			let function = (0..self.sema.decls.functions.len())
				.map(|index| FunctionIdx::new(index as u32))
				.find(|&function| {
					let decl =
						&self.sema.decls.functions[usize::from(function)];
					self.sema.decls.file_id(decl.loc) == self.file
						&& self
							.strings
							.resolve(self.sema.decls.name(function).inner)
							== Some(name)
				})
				.unwrap_or_else(|| panic!("no function `{name}`"));
			self.sema
				.owner_body(BodyOwner::Function(function))
				.expect("a function with a block has a body")
		}

		/// What `locals_at` offers in `function` at the comment `// {mark}`,
		/// each as its name and the line it is declared on (`x@3`), which
		/// tells shadowed locals apart.
		fn visible(&self, function: &str, mark: &str) -> Vec<String> {
			let offset = self
				.source
				.find(&format!("// {mark}"))
				.unwrap_or_else(|| panic!("no `// {mark}`"));
			let body = self.body(function);
			body.locals_at(TextOffset::from(offset as u32))
				.into_iter()
				.map(|local| {
					let name = body.local(local).name;
					let line = self.source[..usize::from(name.span.start)]
						.matches('\n')
						.count() + 1;
					format!(
						"{}@{line}",
						self.strings.resolve(name.inner).unwrap()
					)
				})
				.collect()
		}
	}

	/// At every use of a local the checker resolved, `locals_at` offers
	/// that local for its name: the scopes say what the lookup found.
	#[test]
	fn locals_at_agrees_with_the_checker() {
		let case = Case::new(indoc! {"
			func f(a: u32, c: u32, mut b: u32) -> u32 {
			    local x = a;
			    local x = x + b;
			    b = x;
			    block {
			        local x = b;
			        local y = x;
			        b = y;
			    }
			    if (a == 0) {
			        local z = x;
			        b = z;
			    } else {
			        local z = a;
			        b = z;
			    }
			    local (p, q) = (x, b);
			    match (a) {
			        0 | 1 => p,
			        n => n + q,
			    }
			}
			func g(o: Ordering) -> i8 {
			    local mut n: i8 = 0;
			    loop {
			        local d: i8 = 1;
			        n = n + d;
			        break;
			    }
			    match (o) {
			        Ordering::Less => n,
			        m => n,
			    }
			}
		"});
		case.sema.diagnostics.iter().for_each(|diagnostic| {
			assert!(
				diagnostic.severity
					< codespan_reporting::diagnostic::Severity::Error,
				"{diagnostic:?}"
			);
		});
		let mut checked = 0;
		for (site, &reference) in &case.sema.resolutions.by_site {
			let span = site.span();
			let Reference::Local { owner, local, .. } = reference else {
				continue;
			};
			if span.file_id != case.file {
				continue;
			}
			let body = case.sema.owner_body(owner).unwrap();
			let offered = body.locals_at(span.span.start);
			let name = body.local(local).name.inner;
			let same_name: Vec<_> = offered
				.into_iter()
				.filter(|&other| body.local(other).name.inner == name)
				.collect();
			assert_eq!(
				body.local_named_at(span.span.start, name),
				Some(local),
				"`local_named_at` at {}",
				case.source[usize::from(span.span.start)..]
					.lines()
					.next()
					.unwrap()
			);
			assert_eq!(
				same_name,
				[local],
				"at {}",
				case.source[usize::from(span.span.start)..]
					.lines()
					.next()
					.unwrap()
			);
			checked += 1;
		}
		assert!(checked > 20, "only {checked} uses checked");
	}

	/// What `operand_with_span` finds in `function` at `object`, which
	/// starts the one occurrence of `written` in the source, and its type.
	fn operand(
		case: &Case<'_>,
		function: &str,
		written: &str,
		object: &str,
	) -> (Operand, String) {
		assert!(written.starts_with(object));
		let mut found = case.source.match_indices(written);
		let (start, _) =
			found.next().unwrap_or_else(|| panic!("no `{written}`"));
		assert!(found.next().is_none(), "`{written}` is written twice");
		let start = start as u32;
		let span = TextSpan::from(start..start + object.len() as u32);
		let ast = case.graph.ast(case.file);
		// The outermost one written there: a child comes before its parent.
		let expr = ast
			.exprs
			.spans
			.iter()
			.enumerate()
			.filter(|&(_, &at)| at == span)
			.map(|(index, _)| ExprId(index as u32))
			.next_back()
			.unwrap_or_else(|| panic!("no expression `{object}`"));
		let body = case.body(function);
		let operand = body
			.operand_of(ast, expr)
			.unwrap_or_else(|| panic!("nothing at `{object}`"));
		let ty = case
			.sema
			.type_formatter(&case.strings)
			.display_type(body.operand_ty(operand));
		(operand, ty)
	}

	fn is_local(body: &Body, operand: Operand) -> bool {
		matches!(
			operand,
			Operand::Value(value) if matches!(body.kind(value), ExprKind::Local(_))
		)
	}

	const RECEIVERS: &str = indoc! {"
		memory heap: u32;
		struct Inner(v: u32);
		impl Inner {
		    pub func get(self: heap::&Self) -> u32 { self.*.v }
		}
		struct Outer(inner: Inner, n: u32);
	"};

	/// The object of a field through a pointer is the pointer as written,
	/// not the `Deref` place `p.n` goes through, which has `p`'s span.
	#[test]
	fn an_object_through_a_pointer_is_the_pointer() {
		let source = format!(
			"{RECEIVERS}func f(o: Outer, p: heap::*Outer) {{
			    local a = o.n;
			    local b = p.n;
			}}"
		);
		let case = Case::new(&source);
		let body = case.body("f");
		let (value, ty) = operand(&case, "f", "o.n", "o");
		assert!(is_local(body, value));
		assert_eq!(ty, "Outer");
		let (pointer, ty) = operand(&case, "f", "p.n", "p");
		assert!(is_local(body, pointer));
		assert_eq!(ty, "heap::*Outer");
	}

	/// A place a field access keeps has no value at its span: `p.inner` in
	/// `p.inner.v`, `p.*` in `p.*.n`.
	#[test]
	fn an_object_kept_a_place_is_the_place() {
		let source = format!(
			"{RECEIVERS}func f(p: heap::*Outer) {{
			    local a = p.inner.v;
			    local b = p.*.n;
			}}"
		);
		let case = Case::new(&source);
		let body = case.body("f");
		let (inner, ty) = operand(&case, "f", "p.inner.v", "p.inner");
		let Operand::Place(inner) = inner else {
			panic!("`p.inner` is a value");
		};
		assert!(matches!(body.place(inner).kind, PlaceKind::Field { .. }));
		assert_eq!(ty, "Inner");
		let (pointee, ty) = operand(&case, "f", "p.*.n", "p.*");
		let Operand::Place(pointee) = pointee else {
			panic!("`p.*` is a value");
		};
		assert!(matches!(body.place(pointee).kind, PlaceKind::Deref { .. }));
		assert_eq!(ty, "Outer");
	}

	/// A method's receiver is the value written, not what the checker adds
	/// around it at its span: `q.*.&` for an exclusive `q` given to a
	/// `self: heap::&Self` method.
	#[test]
	fn a_receiver_is_the_value_written() {
		let source = format!(
			"{RECEIVERS}func f(q: heap::*Inner) -> u32 {{
			    q.get()
			}}"
		);
		let case = Case::new(&source);
		let body = case.body("f");
		let (receiver, ty) = operand(&case, "f", "q.get", "q");
		assert!(is_local(body, receiver));
		assert_eq!(ty, "heap::*Inner");
	}

	/// Empty argument tuples must not hide a call's result at its span.
	#[test]
	fn a_call_receiver_is_its_result() {
		let source = indoc! {"
		    struct Empty();
		    impl Empty { pub func id(self: Self) -> Self { self } }
		    struct Caller();
		    impl Call for Caller {
		        type Args = ();
		        type Result = f32;
		        func call(self: Self, args: ()) -> f32 { 1.0 }
		    }
		    func make() -> f32 { 1.0 }
		    func consume_unit(args: ()) -> f32 { 1.0 }
		    func f(x: f32, cb: func() -> f32, c: Caller) {
		        local g = make;
		        _ = x.trunc().abs();
		        _ = x.trunc{}.ceil();
		        _ = make().floor();
		        _ = consume_unit().floor();
		        _ = make{}.floor();
		        _ = g().floor();
		        _ = g{}.floor();
		        _ = cb().floor();
		        _ = c().floor();
		        _ = Empty().id();
		        _ = Empty{}.id();
		    }
		"};
		let case = Case::new(source);
		assert!(
			case.sema.diagnostics().is_empty(),
			"{:?}",
			case.sema.diagnostics()
		);
		let body = case.body("f");
		let ast = case.graph.ast(case.file);
		for (written, object, expected) in [
			("x.trunc().abs", "x.trunc()", "f32"),
			("x.trunc{}.ceil", "x.trunc{}", "f32"),
			("make().floor", "make()", "f32"),
			("consume_unit().floor", "consume_unit()", "f32"),
			("make{}.floor", "make{}", "f32"),
			("g().floor", "g()", "f32"),
			("g{}.floor", "g{}", "f32"),
			("cb().floor", "cb()", "f32"),
			("c().floor", "c()", "f32"),
			("Empty().id", "Empty()", "Empty"),
			("Empty{}.id", "Empty{}", "Empty"),
		] {
			let (value, ty) = operand(&case, "f", written, object);
			assert_eq!(ty, expected, "{object}");
			let Operand::Value(value) = value else {
				panic!("`{object}` is a place");
			};
			let args = match body.kind(value) {
				ExprKind::Call { args, .. }
				| ExprKind::AbstractCall { args, .. }
				| ExprKind::AbstractMethodCall { args, .. }
				| ExprKind::MethodCall { args, .. }
				| ExprKind::CallRef { args, .. } => args,
				ExprKind::StructConstructor { fields, .. } => fields,
				_ => panic!("`{object}` is not a call or construction"),
			};
			let expr = ast
				.exprs
				.spans
				.iter()
				.position(|&span| span == body.span(value))
				.map(|index| ExprId(index as u32))
				.unwrap();
			let Expression::Call { arguments, .. } = ast.expr(expr) else {
				panic!("`{object}` is not written as a call");
			};
			assert_eq!(
				body.span(args),
				ast.arguments_span(arguments),
				"{object}"
			);
		}
	}

	/// An access with no name after its `.` still builds its object, which
	/// completion reads.
	#[test]
	fn an_unfinished_access_keeps_its_object() {
		let source = format!(
			"{RECEIVERS}func f(o: Outer, p: heap::*Outer) {{
			    local a = o.;
			    local b = p.inner.;
			}}"
		);
		let case = Case::recovered(&source);
		let body = case.body("f");
		let (object, ty) = operand(&case, "f", "o.;", "o");
		assert!(is_local(body, object));
		assert_eq!(ty, "Outer");
		let (inner, ty) = operand(&case, "f", "p.inner.;", "p.inner");
		assert!(matches!(inner, Operand::Place(_)));
		assert_eq!(ty, "Inner");
	}

	/// A tuple of one and an ascription add no node: what they hold is
	/// looked through, nested too.
	#[test]
	fn a_parenthesized_or_ascribed_object_is_its_value() {
		let source = format!(
			"{RECEIVERS}func f(o: Outer) {{
			    local a = (o).n;
			    local b = (o: Outer).n;
			    local c = ((o: Outer)).n;
			}}"
		);
		let case = Case::new(&source);
		let body = case.body("f");
		for (written, object) in [
			("(o).n", "(o)"),
			("(o: Outer).n", "(o: Outer)"),
			("((o: Outer)).n", "((o: Outer))"),
		] {
			let (operand, ty) = operand(&case, "f", written, object);
			assert!(is_local(body, operand), "`{object}`");
			assert_eq!(ty, "Outer", "`{object}`");
		}
	}

	/// An ascribed literal is the literal, which coercion gave the type.
	#[test]
	fn an_ascribed_literal_has_its_type() {
		let source = "func f() -> u8 {\n    (5: u8).add(1)\n}\n";
		let case = Case::new(source);
		let body = case.body("f");
		let (literal, ty) = operand(&case, "f", "(5: u8).add", "(5: u8)");
		assert!(matches!(
			literal,
			Operand::Value(value) if matches!(body.kind(value), ExprKind::Int(_))
		));
		assert_eq!(ty, "u8");
	}

	#[test]
	fn a_local_is_in_scope_after_its_statement() {
		let case = Case::new(indoc! {"
			func f(a: u32) {
			    // start
			    local x: u32 = a;
			    local x: u32 =
			        // value
			        x;
			    // after
			}
		"});
		assert_eq!(case.visible("f", "start"), ["a@1"]);
		// The value of `local x` is built before its `x` is in scope.
		assert_eq!(case.visible("f", "value"), ["x@3", "a@1"]);
		assert_eq!(case.visible("f", "after"), ["x@4", "a@1"]);
	}

	#[test]
	fn a_block_or_a_branch_keeps_its_locals() {
		let case = Case::new(indoc! {"
			func f(c: Bool) {
			    local a: u32 = 1;
			    if (c) {
			        local x: u32 = a;
			        // then
			    } else {
			        local x: u32 = a;
			        // else
			    }
			    // after
			}
		"});
		assert_eq!(case.visible("f", "then"), ["x@4", "a@2", "c@1"]);
		assert_eq!(case.visible("f", "else"), ["x@7", "a@2", "c@1"]);
		assert_eq!(case.visible("f", "after"), ["a@2", "c@1"]);
	}

	#[test]
	fn an_arm_binds_after_its_pattern() {
		let case = Case::new(indoc! {"
			func f(a: u32) -> u32 {
			    match (a) {
			        0 => {
			            // first
			            a
			        }
			        n => {
			            // second
			            n
			        }
			    }
			}
		"});
		assert_eq!(case.visible("f", "first"), ["a@1"]);
		assert_eq!(case.visible("f", "second"), ["n@7", "a@1"]);
	}

	#[test]
	fn a_literal_reaches_no_local_around_it() {
		let case = Case::new(indoc! {"
			memory heap: u32;
			func f(a: u32) {
			    local s: heap::&[u32] = [
			        // element
			        1,
			    ];
			}
		"});
		assert_eq!(case.visible("f", "element"), Vec::<String>::new());
	}

	/// Inside a literal an outer local cannot be used, but a name there
	/// still refers to it (E2108), so it hides an item of its name.
	#[test]
	fn a_local_behind_static_data_still_takes_its_name() {
		let source = indoc! {"
			memory heap: u32;
			const x: u32 = 5;
			func f(x: u32) -> heap::&[u32] {
			    [x]
			}
		"};
		let case = Case::new(source);
		let body = case.body("f");
		let at = TextOffset::from(source.find("[x]").unwrap() as u32 + 1);
		assert!(body.locals_at(at).is_empty());
		let found =
			body.local_named_at(at, body.local(LocalIdx::new(0)).name.inner);
		assert_eq!(found, Some(LocalIdx::new(0)));
		// The checker's lookup recorded the same local for that use.
		let (_, &reference) = case
			.sema
			.resolutions
			.by_site
			.iter()
			.find(|(site, _)| {
				let span = site.span();
				span.file_id == case.file && span.span.start == at
			})
			.unwrap();
		assert!(matches!(
			reference,
			Reference::Local { local, .. } if local == LocalIdx::new(0)
		));
	}

	/// The labels a jump at `// mark` can name, each with its kind.
	fn labels(case: &Case, function: &str, mark: &str) -> Vec<String> {
		let offset = case.source.find(&format!("// {mark}")).unwrap();
		let body = case.body(function);
		body.labels_at(TextOffset::from(offset as u32))
			.into_iter()
			.map(|target| {
				let kind = body.target_kind(target);
				let label = body.target(target).label;
				let name = case.strings.resolve(label.unwrap().inner);
				format!("{} {kind:?}", name.unwrap())
			})
			.collect()
	}

	#[test]
	fn labels_at_lists_the_nearest_label_of_each_name() {
		let case = Case::new(indoc::indoc! {"
			func f() {
			    loop :outer {
			        block :inner {
			            loop :outer {
			                // innermost
			            }
			            // between
			        }
			    }
			    // after
			}
		"});
		assert_eq!(
			labels(&case, "f", "innermost"),
			["outer Loop", "inner Block"]
		);
		assert_eq!(
			labels(&case, "f", "between"),
			["inner Block", "outer Loop"]
		);
		assert_eq!(labels(&case, "f", "after"), Vec::<String>::new());
	}

	#[test]
	fn nothing_is_in_scope_outside_the_body() {
		let case = Case::new("func f(a: u32) {}\n// outside\n");
		assert_eq!(case.visible("f", "outside"), Vec::<String>::new());
	}

	#[test]
	fn an_expression_node_stays_small() {
		assert!(std::mem::size_of::<ExprKind>() <= 24);
	}

	#[test]
	fn a_pattern_node_stays_small() {
		assert!(std::mem::size_of::<PatternKind>() <= 16);
	}

	fn written_pattern(case: &Case<'_>, written: &str) -> ast::PatId {
		let start = case.source.rfind(written).unwrap() as u32;
		let span = TextSpan::from(start..start + written.len() as u32);
		let ast = case.graph.ast(case.file);
		fn find(
			ast: &AST,
			pattern: ast::PatId,
			span: TextSpan,
		) -> Option<ast::PatId> {
			if ast.pattern_span(pattern) == span {
				return Some(pattern);
			}
			match ast.pattern(pattern) {
				ast::Pattern::Or(children) => ast
					.list(children)
					.iter()
					.find_map(|&child| find(ast, child, span)),
				ast::Pattern::Destructure(
					ast::Destructure::Tuple { elements }
					| ast::Destructure::Struct { elements, .. },
				) => {
					ast.list(elements).iter().find_map(|element| match *element
					{
						ast::PatternElement::Pattern(child) => {
							find(ast, child, span)
						}
						_ => None,
					})
				}
				ast::Pattern::Destructure(ast::Destructure::NamedStruct {
					fields,
					..
				}) => ast.list(fields).iter().find_map(|item| match item {
					ast::PatternFieldItem::Field(field) => {
						field.pattern.and_then(|child| find(ast, child, span))
					}
					_ => None,
				}),
				_ => None,
			}
		}
		ast.exprs
			.kinds
			.iter()
			.find_map(|expression| match *expression {
				Expression::Match { arms, .. } => ast
					.list(arms)
					.iter()
					.find_map(|arm| find(ast, arm.pattern, span)),
				_ => None,
			})
			.unwrap_or_else(|| panic!("no pattern `{written}`"))
	}

	#[test]
	fn pattern_lookup_unwraps_tuples_but_preserves_alternatives() {
		let case = Case::new(
			"func f(value: Bool) { match (value) { ((_,)) | const False => {} } }",
		);
		let ast = case.graph.ast(case.file);
		let body = case.body("f");
		let wrapped = body
			.pattern_of(ast, written_pattern(&case, "((_,))"))
			.unwrap();
		assert_eq!(
			Some(wrapped),
			body.pattern_of(ast, written_pattern(&case, "_"))
		);
		assert!(matches!(body.pattern(wrapped), PatternKind::Wildcard));
		assert_eq!(body.pattern_ty(wrapped), TypeIndex::BOOL);
		let alternatives = body
			.pattern_of(ast, written_pattern(&case, "((_,)) | const False"))
			.unwrap();
		assert!(matches!(body.pattern(alternatives), PatternKind::Or(_)));
	}

	#[test]
	fn pattern_lookup_prefers_written_destructures_over_synthetic_nodes() {
		for pattern in [
			"Pair(a, b)",
			"Pair{ first: a, second: b }",
			"Pair{..}",
			"Pair(..)",
		] {
			let source = format!(
				"struct Pair(first: u32, second: Bool);
				 func f(value: Pair) {{ match (value) {{ {pattern} => {{}} }} }}"
			);
			let case = Case::new(&source);
			let ast = case.graph.ast(case.file);
			let body = case.body("f");
			let written = written_pattern(&case, pattern);
			let span = ast.pattern_span(written);
			assert!(
				body.pat_spans
					.iter()
					.filter(|&&found| found == span)
					.count() >= 2
			);
			let checked = body.pattern_of(ast, written).unwrap();
			assert!(matches!(
				body.pattern(checked),
				PatternKind::Fields { .. }
			));
			assert_eq!(
				case.sema
					.type_formatter(&case.strings)
					.display_type(body.pattern_type_of(ast, written).unwrap()),
				"Pair"
			);
		}
	}

	#[test]
	fn pattern_lookup_retains_error_types_and_never_uses_another_body() {
		let case = Case::new(
			"func f(value: u8) { match (value) { (999) => {}, _ => {} } }
			 func g(value: Bool) { match (value) { target => {} } }",
		);
		let ast = case.graph.ast(case.file);
		let body = case.body("f");
		let written = written_pattern(&case, "(999)");
		let checked = body.pattern_of(ast, written).unwrap();
		assert!(matches!(body.pattern(checked), PatternKind::Error));
		assert_eq!(body.pattern_type_of(ast, written), Some(TypeIndex::U8));
		assert_eq!(case.body("g").pattern_type_of(ast, written), None);
		assert_eq!(
			body.pattern_type_of(ast, written_pattern(&case, "target")),
			None
		);
	}

	/// Recovery nodes are found through the same exact source spans as
	/// other checked data. A synthetic field tuple can share the owner's
	/// span, so inspect every error at that span here.
	fn error_pattern_types(case: &Case<'_>, written: &str) -> Vec<String> {
		let start = case.source.rfind(written).unwrap();
		let span = TextSpan::from(start as u32..(start + written.len()) as u32);
		let body = case.body("f");
		body.pat_spans
			.iter()
			.enumerate()
			.filter(|&(at, &found)| {
				found == span
					&& matches!(body.pat_kinds[at], PatternKind::Error)
			})
			.map(|(at, _)| {
				case.sema
					.type_formatter(&case.strings)
					.display_type(body.pat_types[at])
			})
			.collect()
	}

	#[test]
	fn erroneous_literal_patterns_keep_the_subject_type() {
		let case = Case::new(
			"func f(value: u8) { match (value) { 999 => {}, _ => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::IntegerLiteralOutOfRange]);
		assert_eq!(error_pattern_types(&case, "999"), ["u8"]);
		let mut sema = case.sema;
		assert!(crate::tir::lower(&mut sema, &case.strings).is_err());
	}

	#[test]
	fn rejected_local_tests_keep_the_original_subject_type() {
		let case =
			Case::new("func f(value: Bool) { local const True = value; }");
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::RefutablePatternInLocal]);
		assert_eq!(error_pattern_types(&case, "const True"), ["Bool"]);
	}

	#[test]
	fn rejected_equality_keeps_the_original_subject_type() {
		let case = Case::new(
			"const BAD: f32 = 1.0;
			 func f(value: f32) { match (value) { const BAD => {}, _ => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		assert_eq!(error_pattern_types(&case, "const BAD"), ["f32"]);
	}

	#[test]
	fn rejected_local_literals_keep_types_without_cascades_or_losing_bindings()
	{
		let case = Case::new(
			"func f(value: (Bool, u8, u32)) -> u32 {
			    local ('x', 999, kept) = value;
			    kept
			 }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::RefutablePatternInLocal]);
		assert_eq!(error_pattern_types(&case, "'x'"), ["Bool"]);
		assert_eq!(error_pattern_types(&case, "999"), ["u8"]);
		let body = case.body("f");
		let kept = body
			.locals
			.iter()
			.find(|local| {
				case.strings.resolve(local.name.inner) == Some("kept")
			})
			.unwrap();
		assert_eq!(kept.ty, TypeIndex::U32);
	}

	#[test]
	fn rejected_local_constants_still_resolve_without_compatibility_cascades() {
		let case = Case::new(
			"const N: u32 = 1;
			 func f(value: Bool) { local const N = value; }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::RefutablePatternInLocal]);
		assert_eq!(error_pattern_types(&case, "const N"), ["Bool"]);
		let start = case.source.rfind("N =").unwrap() as u32;
		let site = Site::Value(SourceSpan::new(
			case.file,
			TextSpan::from(start..start + 1),
		));
		let Some(Reference::Item { item, .. }) =
			case.sema.resolutions.by_site.get(&site)
		else {
			panic!("a rejected constant test must still resolve its name")
		};
		assert!(matches!(
			case.sema.declaration_kind(*item),
			crate::tir::DeclKind::Const(_)
		));
		assert_eq!(
			case.strings.resolve(case.sema.decls.item(*item).name.inner),
			Some("N")
		);
	}

	#[test]
	fn rejected_local_constants_still_report_unresolved_names() {
		let case =
			Case::new("func f(value: Bool) { local const MISSING = value; }");
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[
			DiagnosticCode::RefutablePatternInLocal,
			DiagnosticCode::UndeclaredIdentifier,
		]);
		assert_eq!(error_pattern_types(&case, "const MISSING"), ["Bool"]);
	}

	#[test]
	fn incompatible_destructuring_keeps_its_subject_but_not_guessed_child_types()
	 {
		let case = Case::new(
			"func f(value: Bool) { match (value) { (left, right) => {}, _ => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::TypeMistmatch]);
		assert_eq!(error_pattern_types(&case, "(left, right)"), ["Bool"]);
		let body = case.body("f");
		for local in &body.locals[1..] {
			assert_eq!(local.ty, TypeIndex::ERROR);
		}
	}

	#[test]
	fn synthetic_field_tuple_errors_keep_the_field_type() {
		let case = Case::new(
			"struct W(value: (u8, Bool));
			 func f(value: W) { match (value) { W(a, b, c) => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::ArgumentCountMismatch]);
		assert_eq!(error_pattern_types(&case, "W(a, b, c)"), ["(u8, Bool)"]);
	}

	#[test]
	fn erroneous_enum_repr_patterns_keep_the_enum_type() {
		let case = Case::new(
			"enum Flag(value: u8) { A = 0 }
			 func f(value: Flag) { match (value) { Flag(0) => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_codes(&[DiagnosticCode::TestInEnumRepr]);
		assert_eq!(error_pattern_types(&case, "Flag(0)"), ["Flag"]);
	}

	#[test]
	fn unknown_subjects_do_not_acquire_a_type_from_an_invalid_pattern() {
		let case = Case::new(
			"func f() { match (missing) { const BAD => {}, _ => {} } }",
		);
		DiagnosticView::new(
			"typecheck",
			case.sema.diagnostics(),
			&case.graph.files,
		)
		.assert_error_saying("cannot find");
		assert_eq!(error_pattern_types(&case, "const BAD"), ["{unknown}"]);
	}
}
