//! The syntax tree, as written: what the parser produces and what the
//! checker and the formatter read. The lexer and the parser are its two
//! submodules.

use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

// Compatibility exports for existing compiler consumers.
pub use crate::symbols::{Keyword, StringInterner};

use std::marker::PhantomData;

use crate::{diagnostics::TextSpan, index::index_newtype, vfs::FileId};

mod lexer;
mod parser;
#[cfg(test)]
mod tests;

#[cfg(feature = "bench")]
#[doc(hidden)]
pub use lexer::bench_lex_to_eof;
pub use parser::Parser;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
	Line,
	Doc,
}

#[derive(Clone, Copy)]
pub struct Comment {
	pub span: TextSpan,
	pub kind: CommentKind,
}

pub struct CommentMap(pub Box<[Comment]>);

/// What parsing a file gives, kept apart by who reads it: the tree, which
/// the checker reads; the comments, which only the formatter and the editor
/// do; and what the parser reported.
pub struct Parsed {
	pub ast: AST,
	pub comments: CommentMap,
	pub diagnostics: Vec<Diagnostic<FileId>>,
}

impl CommentMap {
	/// Returns all comments whose spans fall entirely within `[start, end)`.
	pub fn between(&self, start: u32, end: u32) -> &[Comment] {
		let lo = self.0.partition_point(|c| c.span.end <= start);
		let hi = self.0.partition_point(|c| c.span.start < end);
		&self.0[lo..hi]
	}
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum BinaryOp {
	// Arithmetic
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	// Comparison
	Eq,
	NotEq,
	Less,
	LessEq,
	Greater,
	GreaterEq,
	// Logical
	And,
	Or,
	// Assignment
	Assign,
	AddAssign,
	SubAssign,
	MulAssign,
	DivAssign,
	RemAssign,
	BitAndAssign,
	BitOrAssign,
	BitXorAssign,
	LeftShiftAssign,
	RightShiftAssign,
	// Bitwise
	BitAnd,
	BitOr,
	BitXor,
	LeftShift,
	RightShift,
}

impl BinaryOp {
	pub const fn as_str(&self) -> &'static str {
		match self {
			BinaryOp::Add => "+",
			BinaryOp::Sub => "-",
			BinaryOp::Mul => "*",
			BinaryOp::Div => "/",
			BinaryOp::Rem => "%",
			BinaryOp::Eq => "==",
			BinaryOp::NotEq => "!=",
			BinaryOp::Less => "<",
			BinaryOp::LessEq => "<=",
			BinaryOp::Greater => ">",
			BinaryOp::GreaterEq => ">=",
			BinaryOp::And => "&&",
			BinaryOp::Or => "||",
			BinaryOp::Assign => "=",
			BinaryOp::AddAssign => "+=",
			BinaryOp::SubAssign => "-=",
			BinaryOp::MulAssign => "*=",
			BinaryOp::DivAssign => "/=",
			BinaryOp::RemAssign => "%=",
			BinaryOp::BitAndAssign => "&=",
			BinaryOp::BitOrAssign => "|=",
			BinaryOp::BitXorAssign => "^=",
			BinaryOp::LeftShiftAssign => "<<=",
			BinaryOp::RightShiftAssign => ">>=",
			BinaryOp::BitAnd => "&",
			BinaryOp::BitOr => "|",
			BinaryOp::BitXor => "^",
			BinaryOp::LeftShift => "<<",
			BinaryOp::RightShift => ">>",
		}
	}
}

impl std::fmt::Display for BinaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
}

#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum UnaryOp {
	InvertSign,
	Not,
	BitNot,
}

impl UnaryOp {
	pub fn as_str(&self) -> &'static str {
		match self {
			UnaryOp::InvertSign => "-",
			UnaryOp::Not => "!",
			UnaryOp::BitNot => "^",
		}
	}
}

impl std::fmt::Display for UnaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
}

#[derive(Clone)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Spanned<T> {
	pub inner: T,
	pub span: TextSpan,
}

impl<T: Copy> Copy for Spanned<T> {}

/// An expression, in its file's [`AST`]: children by id, lists by
/// [`List`], its span in the column beside it.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Expression {
	Error,
	/// `1`. Always the raw, non-negative magnitude as written — `-1` is a
	/// separate `Unary { InvertSign, .. }` node wrapping this, never folded
	/// in here. Stored as `u64` (not `i64`) so the full range a literal can
	/// validly denote — up to `u64::MAX` directly, or up to `i64::MIN`'s
	/// magnitude when negated — is representable before a concrete target
	/// type decides the final signed/unsigned interpretation.
	Int {
		value: u64,
	},
	/// `1.0` / `3.4e2`. Carries no payload — the text is recovered from the
	/// span and parsed against the *resolved target type* in TIR
	/// (`coerce_float`), because the correct rounding (f32 vs f64)
	/// isn't known until then. Same span-only treatment as `Char` / `String`.
	Float,
	/// `-{expr}`; the operator is where the expression starts
	/// ([`AST::operator_span`]).
	Unary {
		operator: UnaryOp,
		operand: ExprId,
	},
	/// `{expr} + {expr}`; the operator is written at `operator_start`
	/// ([`AST::operator_span`]).
	Binary {
		operator: BinaryOp,
		operator_start: u32,
		left: ExprId,
		right: ExprId,
	},
	/// `{expr}(a, b)`: a call, or the construction of a struct, by
	/// position. A callee that is an [`Expression::ObjectAccess`] makes it
	/// a method call (`x.m::<T>(a)`); a parenthesized one, `(x.f)(a)`, is a
	/// call of the field's value. The arguments are spanned from the `(` at
	/// `open` to the end of the call ([`AST::arguments_span`]).
	Call {
		callee: ExprId,
		arguments: List<ExprId>,
		open: u32,
	},
	/// `{expr}({ x: a, y })`: the same, naming each parameter (or field).
	/// The named list is the call's only argument, spanned by its braces.
	NamedCall {
		callee: ExprId,
		arguments: List<NamedArgument>,
		braces: TextSpan,
	},
	/// `{expr}.{member}`, or `{expr}.{member}::<...>`: the type arguments
	/// are only meaningful when it is called, which makes it a method
	/// call; the checker rejects them on a field.
	ObjectAccess {
		object: ExprId,
		member: SegmentId,
	},
	/// `{expr}.*`
	Deref {
		pointer: ExprId,
	},
	/// `{expr}.&` — always produces a shared reference.
	AddressOf {
		value: ExprId,
	},
	/// `return {expr}`
	Return {
		value: Option<ExprId>,
	},
	/// `block :label { ... }`, or a construct's own block where an
	/// expression is expected (an `else` branch, a match arm), which has no
	/// label. A keyword block's span starts before its braces.
	Block {
		label: Option<Spanned<SymbolU32>>,
		block: BlockId,
	},
	/// `break (:{label})? {expr}?`
	Break {
		label: Option<Spanned<SymbolU32>>,
		value: Option<ExprId>,
	},
	/// `if {expr} { ... } else ...`; an `else` is a block or another `if`.
	IfElse {
		condition: ExprId,
		then_block: BlockId,
		else_block: Option<ExprId>,
	},
	/// `match {expr} { {pattern} => { ... }, ... }`
	Match {
		scrutinee: ExprId,
		arms: List<MatchArm>,
	},
	/// `continue (:{label})?`
	Continue {
		label: Option<Spanned<SymbolU32>>,
	},
	/// `loop :label { ... }`
	Loop {
		label: Option<Spanned<SymbolU32>>,
		block: BlockId,
	},
	/// `_` — discard in value position (e.g. `_ = expr;`)
	Placeholder,
	/// Raw quoted string text is recovered from the expression span.
	String,
	/// 'a' — raw source text (including quotes) is recovered from span
	Char,
	/// A `::` separated path: `foo`, `module::Point`, `module::Point::<i32>`.
	Path(List<PathSegment>),
	/// `<Type as Trait>::item` — a qualified path pinning down exactly
	/// which trait's item is meant. Composes with the usual postfix grammar
	/// (`Call`, `ObjectAccess`, `Index`) like any other primary expression,
	/// e.g. `<Type as Trait>::method(x)`.
	QualifiedPath {
		root: QualifiedRootId,
		segments: List<PathSegment>,
	},
	/// `<Type>::item` — a bare bracketed type used as a path root, with no
	/// trait qualification. Distinct from `QualifiedPath`: this doesn't
	/// disambiguate anything (it resolves exactly like the unbracketed
	/// `Type::item` would), it's purely for self-types that can't be
	/// written as a plain path segment (e.g. `<[T]>::method()`).
	Grouped {
		inner: TypeId,
		segments: List<PathSegment>,
	},
	/// `(a, b, c)`, `(a)`, `(a,)` or `()`: any parenthesized list, as
	/// written. One element is that element, which TIR unwraps.
	Tuple {
		elements: List<ExprId>,
	},
	/// `value: Type`, an element of a parenthesized list (`(5: i32)`,
	/// `f(x: u8, y)`) checked against the type it is written with. It
	/// converts nothing.
	Ascription {
		value: ExprId,
		ty: TypeId,
	},
	/// `[a, b, c]`
	ArrayList {
		elements: List<ExprId>,
	},
	/// `[value; count]`; the count is a length, a literal or a constant.
	ArrayRepeat {
		value: ExprId,
		count: ConstId,
	},
	/// `expr[index]`
	Index {
		object: ExprId,
		index: ExprId,
	},
}

const _: () = assert!(size_of::<Expression>() <= 24);

/// `name: expr`, or the shorthand `name` for `name: name`, in a named list.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct NamedArgument {
	pub name: Spanned<SymbolU32>,
	/// `None` means shorthand: `{ name }` is equivalent to `{ name: name }`
	pub value: Option<ExprId>,
}

/// One arm of a `match` expression: `{pattern} => { ... }` or
/// `{pattern} => expr`. The pattern
/// says what each of its terms is on its own: a name binds, a literal
/// compares with that value, a qualified path with that constant.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct MatchArm {
	pub pattern: PatId,
	pub body: ExprId,
}

/// A block's statements, as written between its braces: each statement in
/// order, and the expression written last without a `;`, which is the
/// block's value.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Block {
	pub statements: List<StmtId>,
	/// The last expression, written without `;`: the block's value.
	pub tail: Option<ExprId>,
}

/// One segment of a `::` path, with optional turbofish type args.
/// `Point` → `PathSegment { ident: "Point", type_args: [] }`
/// `Point<i32>` → `PathSegment { ident: "Point", type_args: [i32] }`. The
/// spelling of `type_args` depends on which parser produced the segment —
/// bare `<...>` from `parse_type_path`, turbofish `::<...>` from
/// `parse_value_path` — never both; empty when no type args are provided.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct PathSegment {
	pub ident: Spanned<SymbolU32>,
	pub type_args: List<TypeArgument>,
	/// Where the type arguments are written, from the first to the last;
	/// empty, at the end of the name, when there are none.
	pub args_span: TextSpan,
}

impl PathSegment {
	/// A segment with no type arguments.
	pub fn new(ident: Spanned<SymbolU32>) -> Self {
		Self {
			ident,
			type_args: List::EMPTY,
			args_span: TextSpan::new(ident.span.end, ident.span.end),
		}
	}

	/// The name a member access or a path is missing (`x.` or `a::`, with no
	/// name after it): the error symbol, at the empty span right after the
	/// `.` or `::`. The parser has reported it, so a lookup of it is silent.
	fn missing(at: u32) -> Self {
		Self::new(Spanned {
			inner: Keyword::Error.symbol(),
			span: TextSpan::new(at, at),
		})
	}

	/// The span of the segment: its name through its last type argument.
	pub fn span(&self) -> TextSpan {
		TextSpan::new(self.ident.span.start, self.args_span.end)
	}

	/// Whether no name is written here: the parser reported it already.
	pub fn is_missing(&self) -> bool {
		self.ident.inner == Keyword::Error.symbol()
	}
}

/// A parsed, non-empty `::`-separated path — `i32`, `module::Type`,
/// `Point<i32>` — where an item names a type or a trait.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Path {
	pub segments: List<PathSegment>,
	/// From its first segment's name to its last's, not including any
	/// trailing type arguments ([`AST::path_span`]).
	pub span: TextSpan,
}

/// The `<Type as Trait>` clause of a qualified path (`<Type as
/// Trait>::item`) — its own struct so the whole bracketed clause, the site
/// of a "trait not implemented" error, carries one precise span (exactly
/// `<self_type as trait_path>`, not including the trailing `::item`) rather
/// than that span having to be reconstructed from separately-threaded
/// pieces at every diagnostic call site.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct QualifiedPathRoot {
	pub self_type: TypeId,
	pub trait_path: List<PathSegment>,
	pub span: TextSpan,
}

/// A trait or typeset bound expression.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum BoundExpression {
	/// A bound the parser expected and did not find (`trait X: {`).
	Error,
	/// `Trait` or `module::Trait`
	Path(List<PathSegment>),
	/// `Memory where { Size = u32, Size: UnsignedInt }` — trait bound with
	/// associated-type bindings.
	WithBindings {
		path: List<PathSegment>,
		bindings: List<AssocBinding>,
	},
	/// `Bound1 + Bound2 + Bound3` — multiple bounds joined by `+`.
	BoundList(List<BoundId>),
}

impl Expression {
	pub fn is_block_like(&self) -> bool {
		matches!(
			self,
			Expression::Block { .. }
				| Expression::IfElse { .. }
				| Expression::Loop { .. }
				| Expression::Match { .. }
		)
	}
}

/// A generic parameter declaration: a type, `T` or `T: Bound1 + Bound2`, or
/// a constant, `const N: Type`.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum TypeParam {
	/// A type, with its trait bounds. `None` = unconstrained.
	Type {
		name: Spanned<SymbolU32>,
		bounds: Option<BoundId>,
	},
	/// `const N: Type`, a constant of type `ty`.
	Const {
		const_span: TextSpan,
		name: Spanned<SymbolU32>,
		ty: TypeId,
	},
}

impl TypeParam {
	pub fn name(&self) -> Spanned<SymbolU32> {
		match self {
			Self::Type { name, .. } | Self::Const { name, .. } => *name,
		}
	}
}

/// One argument in a `<...>` list. What it is follows from its own shape: a
/// literal is a constant, and anything else is a type unless `const` marks
/// it as a constant (`const SIZE`).
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum TypeArgument {
	Type(TypeId),
	Const(ConstId),
}

/// A constant argument: `5`, `-1`, `'a'`, or a path marked `const`. An
/// array's length can also be `_`, left to its context.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ConstArgument {
	Literal(Literal),
	Path(List<PathSegment>),
	/// `<Type as Trait>::NAME`.
	QualifiedPath {
		root: QualifiedRootId,
		segments: List<PathSegment>,
	},
	/// `<Type>::NAME`, for a type no path names (`<heap::&[u8; 4]>::SIZE`).
	Grouped {
		inner: TypeId,
		segments: List<PathSegment>,
	},
	Infer,
}

/// A parameter of a function type, `func(i32, self: T)`, named or not.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct FunctionTypeParam {
	pub name: Option<Spanned<SymbolU32>>,
	pub ty: TypeId,
	pub span: TextSpan,
}

/// One entry of a `where { .. }` block, constraining a member of the bound's
/// trait: an associated type (`Size = u32`, `Size: UnsignedInt`) or, marked
/// `const`, an associated constant (`const LEN: u32`, `const LEN = 4`).
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct AssocBinding {
	pub name: Spanned<SymbolU32>,
	pub kind: AssocBindingKind,
	pub span: TextSpan,
}

/// What an [`AssocBinding`] states. The `const` keyword alone tells a
/// constant's entry from a type's.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum AssocBindingKind {
	/// `Size = u32` — the associated type must equal exactly this type.
	Equals(TypeId),
	/// `Size: UnsignedInt` — the associated type must satisfy this bound.
	Bound(BoundId),
	/// `const LEN: u32` — the constant's value must be representable as this
	/// type.
	ConstRepresentable { const_span: TextSpan, ty: TypeId },
	/// `const LEN = 4` — the constant must have this value.
	ConstEquals {
		const_span: TextSpan,
		value: ConstId,
	},
}

/// `*T` = exclusive pointer/slice/array, `&T` = shared, always read-only.
/// No enforcement of "only one exclusive value at a time" — this is a naming
/// convention carried through the type system, not a move-checker.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Ownership {
	Exclusive,
	Shared,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum TypeExpression {
	/// A type the parser expected and did not find, already reported; it
	/// resolves to `ERROR` without a word.
	Error,
	/// `_` — explicit inference placeholder; type-resolution context decides
	/// whether it stays `INFER` or is rejected as `ERROR`.
	Infer,
	/// `!`, the type of an expression that never produces a value.
	Never,
	/// `i32`, `module::Type`, `Point<i32>`, `module::Wrapper<T>` — a flat path
	/// of segments; any segment (including the first) may carry bare
	/// `<...>` generic arguments. Turbofish is never accepted in type
	/// position, only in expression position (see `parse_value_path`).
	Path(List<PathSegment>),
	/// `(T, U, V)`, `(T)`, `(T,)` or `()`: any parenthesized list, as
	/// written. One element is that type, which TIR unwraps.
	Tuple { elements: List<TypeId> },
	/// `func(i32, i32) -> i32`
	Function {
		params: List<FunctionTypeParam>,
		result: Option<TypeId>,
	},
	/// `*u8` or `&u8`; `heap::*u8` names the memory it points into, and
	/// `heap::&[u8]` is a pointer to the slice `[u8]`. The parser accepts
	/// an untagged pointer and the type checker reports it, since a pointer
	/// always needs its memory. The tag is carried on the pointer itself
	/// (rather than as a separate wrapper node) so only a pointer can ever
	/// be tagged, a constraint the parser otherwise has to enforce by hand
	/// against an arbitrary inner type expression.
	Pointer {
		ownership: Ownership,
		memory: Option<List<PathSegment>>,
		inner: TypeId,
	},
	/// `[u8]`, a slice: a run of values in no memory, held by a pointer.
	Slice { inner: TypeId },
	/// `[u8; 5]` or `[u8; N]`, an array: a slice of a known length.
	Array {
		inner: TypeId,
		/// A literal or a constant, as a constant argument is.
		length: ConstId,
	},
	/// `<Type as Trait>::Item` — a qualified path that pins down exactly
	/// which trait's item is meant, disambiguating a name that would
	/// otherwise be ambiguous (or first-match) across multiple bounds/impls
	/// on `self_type`.
	QualifiedPath {
		root: QualifiedRootId,
		segments: List<PathSegment>,
	},
	/// `<Type>::Item` — a bare bracketed type used as a path root, with no
	/// trait qualification. See `Expression::Grouped` for why this is kept
	/// distinct from `QualifiedPath` rather than making its `trait_path`
	/// optional.
	Grouped {
		inner: TypeId,
		segments: List<PathSegment>,
	},
}

const _: () = assert!(size_of::<TypeExpression>() <= 24);
const _: () = assert!(size_of::<ConstArgument>() <= 24);
const _: () = assert!(size_of::<BoundExpression>() <= 24);

/// A pattern, as written. What each term *is* follows from its own shape:
/// a name binds, a literal compares with that value, a qualified path
/// compares with that constant — and `const` marks the one case that is
/// ambiguous, a single-segment name that should compare with a constant
/// instead of binding.
///
/// The parser resolves every term while parsing, so a name reaches the AST
/// already decided — a [`Pattern::Binding`] or a [`Pattern::Constant`] —
/// and never as something a later stage has to reinterpret.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Pattern {
	/// `_`
	Wildcard,
	/// `[mut] name`. A binding written `mut` starts at it, so its span is
	/// [`AST::pattern_mut_span`].
	Binding {
		mutable: bool,
		name: Spanned<SymbolU32>,
	},
	/// A constant, named by a path: `const MAX`, `Ordering::Less`,
	/// `Self::LIMIT`. A path of one segment can only be a constant the
	/// author marked with `const`; a longer one names a constant already.
	Constant {
		path: List<PathSegment>,
	},
	/// `0`, `-1`, `'a'`
	Literal(Literal),
	/// `A | B | C`
	Or(List<PatId>),
	Destructure(Destructure),
	/// A pattern the parser could not read: the diagnostic is already out,
	/// and nothing here can be checked.
	Error,
}

/// Destructuring; each of its children is a pattern of its own.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Destructure {
	/// `(a, .., z)`
	Tuple { elements: List<PatternElement> },
	/// `Name(pat, ..)` or `module::Name(pat, ..)`, written exactly as its
	/// construction is (`Name(1, 2)`), so a pattern and a value read the same
	/// way.
	Struct {
		path: List<PathSegment>,
		elements: List<PatternElement>,
	},
	/// `Name({ field, other: pat, .. })`, as `Name({ x: 1, y: 2 })` constructs
	/// it.
	NamedStruct {
		path: List<PathSegment>,
		fields: List<PatternFieldItem>,
	},
}

/// One entry of a positional list, exactly as written: how many `..` there
/// are and where is a semantic question TIR answers, not a parse-time
/// assumption.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum PatternElement {
	Pattern(PatId),
	/// `..`, at this span.
	Rest(TextSpan),
}

/// One entry of a named list, exactly as written; see [`PatternElement`].
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum PatternFieldItem {
	Field(PatternField),
	/// `..`, at this span.
	Rest(TextSpan),
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct PatternField {
	pub name: Spanned<SymbolU32>,
	/// `None` = shorthand `{ x }`: the field binds a local of its own name,
	/// the same as `{ x: x }`.
	pub pattern: Option<PatId>,
}

const _: () = assert!(size_of::<Pattern>() <= 24);

/// A literal written where a value is compared or given as a type
/// argument: a pattern's, or a constant argument's.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Literal {
	/// `1`; the value is the number itself.
	Int(u64),
	/// `-1`; the value is the magnitude, and the sign is the variant that
	/// holds it — a negative literal is a literal of its own, not a
	/// positive one with a sign attached.
	NegInt(u64),
	/// `'a'`, decoded from the literal's span as a char expression is.
	Char,
	/// `1.5` — the text is recovered from the span, as an expression's
	/// float is. A float has no single value to compare with, so a
	/// pattern refuses it.
	Float,
	/// `"hi"` — the raw text is recovered from the span, as an
	/// expression's string is. A string has no equality, so a pattern
	/// refuses it.
	String,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Statement {
	/// `{expr};`, or a block-like expression with its `;` left out.
	Expression(ExprId),
	/// `local <pattern> [: type] = {expr}`
	LocalDefinition {
		pattern: PatId,
		ty: Option<TypeId>,
		value: ExprId,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
/// What a parameter or a field is bound to, written before a `:`. One left
/// out is no `Binding` at all, and binds nothing as `_` does.
pub enum Binding {
	/// `_`: binds nothing.
	Wildcard(TextSpan),
	/// `name` or `mut name`.
	Name {
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
	},
}

impl Binding {
	/// The name bound, `None` for `_`.
	pub fn name(self) -> Option<Spanned<SymbolU32>> {
		match self {
			Binding::Wildcard(_) => None,
			Binding::Name { name, .. } => Some(name),
		}
	}
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
/// A parameter, written like a struct field: `binding: Type`, or `Type`
/// alone, which binds nothing as `_: Type` does. The receiver is
/// `self: Type`.
pub struct FunctionParam {
	pub binding: Option<Binding>,
	pub ty: TypeId,
}

/// The payload of an attribute.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum AttributeValue {
	/// `#[inline]` — name only, no payload.
	Word,
	/// `#[memory_limits({ min_pages: 1, max_pages: 10 })]` — arguments by
	/// name, written as a call's (`f({ x: 1 })`). What each value may be is
	/// the attribute's to say, where it is resolved.
	Named(List<NamedArgument>),
}

/// A single attribute on an item, e.g. `#[inline]` or
/// `#[memory_limits({ min_pages: 1 })]`.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Attribute {
	pub name: Spanned<SymbolU32>,
	pub value: AttributeValue,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ImplItem {
	/// A method or associated function — TIR distinguishes the two after
	/// parsing, by checking whether the first param is named `self`.
	Function {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		signature: FunctionSignature,
		block: BlockId,
	},
	Constant {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: ExprId,
		attributes: List<Attribute>,
	},
	AssocType {
		/// Always an error to have set — an associated type is only legal in
		/// a trait impl, where visibility comes from the trait. Recorded
		/// anyway so the qualifier can be reported and round-tripped:
		/// dropping it here made the formatter delete `pub` from the source.
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: TypeId,
		attributes: List<Attribute>,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum TraitItem {
	/// A method with an optional default body.
	Function {
		attributes: List<Attribute>,
		signature: FunctionSignature,
		/// `None` = abstract (must be provided by impl); `Some` = default
		/// implementation.
		body: Option<BlockId>,
	},
	/// An associated constant declaration, with an optional default value.
	/// `None` = abstract (must be provided by every impl); `Some` = a
	/// default value impls may omit and inherit as-is.
	Const {
		name: Spanned<SymbolU32>,
		attributes: List<Attribute>,
		ty: TypeId,
		value: Option<ExprId>,
	},
	/// An associated type declaration, optionally with a default value.
	AssociatedType {
		name: Spanned<SymbolU32>,
		attributes: List<Attribute>,
		/// Trait bounds the concrete type must satisfy. `None` = unconstrained.
		bounds: Option<BoundId>,
		/// Used when an impl does not provide this associated type.
		value: Option<TypeId>,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct FunctionSignature {
	pub name: Spanned<SymbolU32>,
	/// Generic type parameters `<T, U: Bound>`. Empty = monomorphic.
	pub type_params: List<TypeParam>,
	pub params: List<FunctionParam>,
	pub result: Option<TypeId>,
}

/// One node of a `use` tree. `use a::b::*` is
/// `Path{a, Path{b, Glob}}`; `use a::{b, c::*}` is `Path{a, Group[Name{b},
/// Path{c, Glob}]}`.
///
/// The two leaf kinds resolve at different times, which is why they stay
/// distinct all the way into TIR rather than collapsing into one "import"
/// node: a `Glob` has to be registered during prescan (`lookup_global_symbol`
/// consults `wildcard_imports` throughout Phase 2, so one registered later
/// would be invisible to earlier lookups), while a `Name` *cannot* be
/// resolved that early — files are prescanned in order, so `use math::add;`
/// in `main.wx` runs before `math.wx`'s items exist.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum UseTree {
	/// `*` — every visible name in the namespace walked to so far.
	Glob { segment: Spanned<SymbolU32> },
	/// A single imported name, optionally renamed: `add`, `add as plus`.
	Name {
		segment: Spanned<SymbolU32>,
		alias: Option<Spanned<SymbolU32>>,
	},
	/// One `::`-separated segment and whatever follows it.
	Path {
		segment: Spanned<SymbolU32>,
		rest: UseTreeId,
	},
	/// `{ .. }` — several subtrees sharing the prefix walked to so far.
	Group {
		segment: Spanned<SymbolU32>,
		branches: List<UseTree>,
		/// The braces, `{` through `}`.
		braces: TextSpan,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct ExportEntry {
	pub name: Spanned<SymbolU32>,
	/// The span of the raw quoted external name.
	pub alias: Option<TextSpan>,
}

impl ExportEntry {
	/// The entry as written: its name through its alias.
	pub fn span(&self) -> TextSpan {
		let end = self.alias.map_or(self.name.span.end, |alias| alias.end);
		TextSpan::new(self.name.span.start, end)
	}
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ImportDeclaration {
	Function {
		signature: FunctionSignature,
	},
	Global {
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: TypeId,
	},
	Memory {
		name: Spanned<SymbolU32>,
		size: TypeId,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ImportEntry {
	Declaration {
		/// The field the host provides it as, a string literal as written
		/// (`"Log": func log(..)`); its own name when left out.
		external_name: Option<TextSpan>,
		declaration: ImportDeclaration,
	},
	/// A source-level import/re-export, not an entity imported from the host.
	Use {
		pub_span: Option<TextSpan>,
		tree: UseTreeId,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct EnumVariant {
	pub name: Spanned<SymbolU32>,
	pub value: Option<ExprId>,
}

/// An entry of an enum body, as written.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum EnumEntry {
	Variant(EnumVariant),
	/// A `..`: the variants name some of the enum's values, and every value of
	/// its repr is valid. It is not a variant. Where it is written, and how
	/// many there are, is for the checker to judge.
	Rest,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Item {
	Function {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		signature: FunctionSignature,
		block: BlockId,
	},
	FunctionDeclaration {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		signature: FunctionSignature,
	},
	/// A package contract member whose implementation is supplied externally.
	PackageFunction {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: List<Attribute>,
		signature: FunctionSignature,
	},
	PackageConst {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		ty: TypeId,
	},
	PackageType {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		type_params: List<TypeParam>,
	},
	Global {
		pub_span: Option<TextSpan>,
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: ExprId,
		attributes: List<Attribute>,
	},
	Export {
		entry: ExportEntry,
	},
	ExportBlock {
		/// Span of the `export` keyword.
		keyword_span: TextSpan,
		entries: List<ExportEntry>,
	},
	Import {
		external_name: TextSpan,
		internal_name: Spanned<SymbolU32>,
		entries: List<ImportEntry>,
		/// The braces, `{` through `}`.
		braces: TextSpan,
	},
	Enum {
		pub_span: Option<TextSpan>,
		repr: Option<TypeId>,
		name: Spanned<SymbolU32>,
		entries: List<EnumEntry>,
		attributes: List<Attribute>,
	},
	/// `impl Type { ... }`
	InherentImpl {
		type_params: List<TypeParam>,
		target: Path,
		items: List<ImplItem>,
	},
	/// `impl Trait for Type { ... }` / `impl<T> Trait for Type<T> { ... }`
	TraitImpl {
		type_params: List<TypeParam>,
		/// Plain path to the trait, e.g. `module::Trait`.
		trait_name: Path,
		target: Path,
		items: List<ImplItem>,
	},
	/// `struct Point(x: i32, y: i32);`, `struct Pair(i32, i32);` — one form
	/// for every struct. A field's name is optional, field by field, like its
	/// `pub`; a struct is constructed by a call, by position always and by
	/// name when every field has one.
	Struct {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		type_params: List<TypeParam>,
		fields: List<StructField>,
	},
	Memory {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		size: TypeId,
	},
	Const {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: ExprId,
		attributes: List<Attribute>,
	},
	Module {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		items: List<Item>,
		/// The braces, `{` through `}`.
		braces: TextSpan,
	},
	ModuleDeclaration {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
	},
	/// A package instance, `package "math" as math;` — instantiates the package the manifest
	/// declares under the key `"math"` and binds it here as `math`. With
	/// `pub`, whoever can see this module can also name the package through
	/// it. Allowed in any module, not just a package's root.
	PackageInstance {
		pub_span: Option<TextSpan>,
		/// The raw quoted manifest key, decoded where it is resolved.
		package: TextSpan,
		alias: Spanned<SymbolU32>,
	},
	Trait {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		/// Supertrait bounds: `trait X: Y + Z { ... }`.  `None` = no bounds.
		supertraits: Option<BoundId>,
		items: List<TraitItem>,
	},
	/// `typeset Name: A + B { T1, T2, ... }` — a closed compile-time set of
	/// concrete types. The optional bound clause after `:` applies to every
	/// member: each member must satisfy `A + B`, and a body generic over the
	/// typeset may rely on those bounds. `None` = no bounds required.
	TypeSet {
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		name: Spanned<SymbolU32>,
		bounds: Option<BoundId>,
		members: List<Path>,
	},
	/// `use math::add;`, `use math::*;`, `use math::{trig::sin, ops::*};` —
	/// brings names from another namespace into this one.
	Use {
		pub_span: Option<TextSpan>,
		tree: UseTreeId,
	},
	/// `type Name = TypeExpr;` or `type Name<T> = TypeExpr;` — a transparent
	/// alias. `body` is `None` only for a bodiless `#[intrinsic] type Name;`
	/// declaration (primitives).
	TypeAlias {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		type_params: List<TypeParam>,
		body: Option<TypeId>,
		attributes: List<Attribute>,
	},
}

#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct StructField {
	pub pub_span: Option<TextSpan>,
	/// `None` for a positional field: `struct Pair(i32, i32);`. A binding's
	/// `mut` is parsed; what it allows is not checked yet.
	pub binding: Option<Binding>,
	pub ty: TypeId,
}

impl Item {
	/// Whether the item ends at its own `}`, so no `;` follows it.
	pub fn is_block_like(&self) -> bool {
		match self {
			Item::Function { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::Enum { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. }
			| Item::Module { .. }
			| Item::Trait { .. }
			| Item::TypeSet { .. } => true,
			Item::Global { .. }
			| Item::Export { .. }
			| Item::Const { .. }
			| Item::PackageFunction { .. }
			| Item::PackageConst { .. }
			| Item::PackageType { .. }
			| Item::Memory { .. }
			| Item::FunctionDeclaration { .. }
			| Item::ModuleDeclaration { .. }
			| Item::TypeAlias { .. }
			| Item::Struct { .. }
			| Item::PackageInstance { .. }
			| Item::Use { .. } => false,
		}
	}

	/// Backfills the attributes parsed ahead of an item onto whichever item
	/// kinds carry an `attributes` field. No-op for kinds that don't.
	pub fn set_attributes(&mut self, attrs: List<Attribute>) {
		match self {
			Item::Function { attributes, .. }
			| Item::FunctionDeclaration { attributes, .. }
			| Item::PackageFunction { attributes, .. }
			| Item::PackageConst { attributes, .. }
			| Item::PackageType { attributes, .. }
			| Item::Trait { attributes, .. }
			| Item::TypeSet { attributes, .. }
			| Item::Const { attributes, .. }
			| Item::Global { attributes, .. }
			| Item::Enum { attributes, .. }
			| Item::TypeAlias { attributes, .. }
			| Item::Memory { attributes, .. }
			| Item::Struct { attributes, .. } => {
				*attributes = attrs;
			}
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::Import { .. }
			| Item::InherentImpl { .. }
			| Item::TraitImpl { .. }
			| Item::Module { .. }
			| Item::ModuleDeclaration { .. }
			| Item::PackageInstance { .. }
			| Item::Use { .. } => {}
		}
	}
}

index_newtype!(
	/// An item, in its file's [`AST`].
	ItemId
);
index_newtype!(
	/// A member of an `impl` block, in its file's [`AST`].
	ImplItemId
);
index_newtype!(
	/// A member of a trait, in its file's [`AST`].
	TraitItemId
);
index_newtype!(
	/// A node of a `use` tree, in its file's [`AST`].
	UseTreeId
);
index_newtype!(
	/// A type expression, in its file's [`AST`].
	TypeId
);
index_newtype!(
	/// A constant argument (a length, a `const` type argument), in its
	/// file's [`AST`].
	ConstId
);
index_newtype!(
	/// A bound, in its file's [`AST`].
	BoundId
);
index_newtype!(
	/// The `<Type as Trait>` of a qualified path, in its file's [`AST`].
	QualifiedRootId
);
index_newtype!(
	/// A pattern, in its file's [`AST`].
	PatId
);
index_newtype!(
	/// An expression, in its file's [`AST`].
	ExprId
);
index_newtype!(
	/// A statement, in its file's [`AST`].
	StmtId
);
index_newtype!(
	/// A block, `{ ... }`, in its file's [`AST`].
	BlockId
);
index_newtype!(
	/// One path segment, in its file's [`AST`]: a member's name.
	SegmentId
);

/// A run of one of the [`AST`]'s lists, read with [`AST::list`]: the
/// segments of a path, the arguments of a segment, the elements of a tuple
/// type. A list is written once, whole, so its items are contiguous.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct List<T> {
	start: u32,
	len: u32,
	#[cfg_attr(any(debug_assertions, test), serde(skip))]
	of: PhantomData<T>,
}

impl<T> Clone for List<T> {
	fn clone(&self) -> Self {
		*self
	}
}

impl<T> Copy for List<T> {}

impl<T> List<T> {
	pub const EMPTY: Self = Self {
		start: 0,
		len: 0,
		of: PhantomData,
	};

	pub fn len(self) -> usize {
		self.len as usize
	}

	pub fn is_empty(self) -> bool {
		self.len == 0
	}

	fn range(self) -> std::ops::Range<usize> {
		self.start as usize..(self.start + self.len) as usize
	}
}

/// What an [`AST`] holds in a list, read with [`AST::list`].
pub trait Listed: Sized {
	fn store(ast: &AST) -> &[Self];
}

/// A list's items in a [`Column`], each with its span, read with
/// [`AST::spanned`].
pub trait InColumn: Listed {
	fn spans(ast: &AST) -> &[TextSpan];
}

/// A node in a [`Column`] that is addressed on its own, by its position.
pub trait Identified: InColumn {
	type Id: Copy;
	#[doc(hidden)]
	fn id(index: u32) -> Self::Id;
}

/// Where the parser writes a list kept in a plain vector.
trait BuildVec: Sized {
	fn vec_mut(builder: &mut AstBuilder) -> &mut Vec<Self>;
}

/// Where the parser writes a list or a node kept in a column.
trait BuildColumn: Sized {
	fn column_mut(builder: &mut AstBuilder) -> &mut ColumnBuilder<Self>;
}

macro_rules! listed {
	($($item:ty => $field:ident),+ $(,)?) => {
		$(impl Listed for $item {
			fn store(ast: &AST) -> &[Self] {
				&ast.$field
			}
		}
		impl BuildVec for $item {
			fn vec_mut(builder: &mut AstBuilder) -> &mut Vec<Self> {
				&mut builder.$field
			}
		})+
	};
}

macro_rules! columns {
	($($item:ty => $field:ident),+ $(,)?) => {
		$(impl Listed for $item {
			fn store(ast: &AST) -> &[Self] {
				&ast.$field.kinds
			}
		}
		impl InColumn for $item {
			fn spans(ast: &AST) -> &[TextSpan] {
				&ast.$field.spans
			}
		}
		impl BuildColumn for $item {
			fn column_mut(builder: &mut AstBuilder) -> &mut ColumnBuilder<Self> {
				&mut builder.$field
			}
		})+
	};
}

macro_rules! identified {
	($($item:ty => $id:ident),+ $(,)?) => {
		$(impl Identified for $item {
			type Id = $id;
			fn id(index: u32) -> $id {
				$id::new(index)
			}
		})+
	};
}

listed! {
	PathSegment => segments,
	TypeArgument => type_args,
	TypeId => type_lists,
	BoundId => bound_lists,
	AssocBinding => assoc_bindings,
	FunctionTypeParam => function_type_params,
	PatId => pat_lists,
	PatternElement => pattern_elements,
	PatternFieldItem => pattern_fields,
	ExprId => expr_lists,
	StmtId => stmt_lists,
	NamedArgument => named_arguments,
	MatchArm => arms,
	Attribute => attributes,
	ExportEntry => export_entries,
	Path => paths,
}

columns! {
	Item => items,
	ImplItem => impl_items,
	TraitItem => trait_items,
	UseTree => use_trees,
	TypeParam => type_params,
	FunctionParam => function_params,
	StructField => struct_fields,
	EnumEntry => enum_entries,
	ImportEntry => import_entries,
}

identified! {
	Item => ItemId,
	ImplItem => ImplItemId,
	TraitItem => TraitItemId,
	UseTree => UseTreeId,
}

/// A column of nodes of one kind, each with its span; a node's id is its
/// position.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
struct Column<K> {
	kinds: Box<[K]>,
	spans: Box<[TextSpan]>,
}

/// A [`Column`] while the parser writes it.
struct ColumnBuilder<K> {
	kinds: Vec<K>,
	spans: Vec<TextSpan>,
}

impl<K> Default for ColumnBuilder<K> {
	fn default() -> Self {
		Self {
			kinds: Vec::new(),
			spans: Vec::new(),
		}
	}
}

impl<K> ColumnBuilder<K> {
	fn push(&mut self, kind: K, span: TextSpan) -> u32 {
		let index = u32::try_from(self.kinds.len()).unwrap();
		self.kinds.push(kind);
		self.spans.push(span);
		index
	}

	fn finish(self) -> Column<K> {
		Column {
			kinds: self.kinds.into_boxed_slice(),
			spans: self.spans.into_boxed_slice(),
		}
	}
}

/// One file's syntax tree: every node lives in a column addressed by id (a
/// child before its parent), and every list is a [`List`], its items
/// contiguous (`notes/ast-arena-plan.md`). The file's own items are
/// [`AST::root`]. It is read only; the parser writes an [`AstBuilder`] and
/// finishes it into one, each vector fitted to its contents.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct AST {
	/// The items written at the top of the file.
	pub root: List<Item>,
	types: Column<TypeExpression>,
	consts: Column<ConstArgument>,
	bounds: Column<BoundExpression>,
	patterns: Column<Pattern>,
	exprs: Column<Expression>,
	stmts: Column<Statement>,
	blocks: Column<Block>,
	qualified_roots: Box<[QualifiedPathRoot]>,
	segments: Box<[PathSegment]>,
	type_args: Box<[TypeArgument]>,
	type_lists: Box<[TypeId]>,
	bound_lists: Box<[BoundId]>,
	assoc_bindings: Box<[AssocBinding]>,
	function_type_params: Box<[FunctionTypeParam]>,
	pat_lists: Box<[PatId]>,
	pattern_elements: Box<[PatternElement]>,
	pattern_fields: Box<[PatternFieldItem]>,
	expr_lists: Box<[ExprId]>,
	stmt_lists: Box<[StmtId]>,
	named_arguments: Box<[NamedArgument]>,
	arms: Box<[MatchArm]>,
	items: Column<Item>,
	impl_items: Column<ImplItem>,
	trait_items: Column<TraitItem>,
	use_trees: Column<UseTree>,
	type_params: Column<TypeParam>,
	function_params: Column<FunctionParam>,
	struct_fields: Column<StructField>,
	enum_entries: Column<EnumEntry>,
	import_entries: Column<ImportEntry>,
	attributes: Box<[Attribute]>,
	export_entries: Box<[ExportEntry]>,
	paths: Box<[Path]>,
}

/// An [`AST`] while the parser writes it.
#[derive(Default)]
struct AstBuilder {
	types: ColumnBuilder<TypeExpression>,
	consts: ColumnBuilder<ConstArgument>,
	bounds: ColumnBuilder<BoundExpression>,
	patterns: ColumnBuilder<Pattern>,
	exprs: ColumnBuilder<Expression>,
	stmts: ColumnBuilder<Statement>,
	blocks: ColumnBuilder<Block>,
	qualified_roots: Vec<QualifiedPathRoot>,
	segments: Vec<PathSegment>,
	type_args: Vec<TypeArgument>,
	type_lists: Vec<TypeId>,
	bound_lists: Vec<BoundId>,
	assoc_bindings: Vec<AssocBinding>,
	function_type_params: Vec<FunctionTypeParam>,
	pat_lists: Vec<PatId>,
	pattern_elements: Vec<PatternElement>,
	pattern_fields: Vec<PatternFieldItem>,
	expr_lists: Vec<ExprId>,
	stmt_lists: Vec<StmtId>,
	named_arguments: Vec<NamedArgument>,
	arms: Vec<MatchArm>,
	items: ColumnBuilder<Item>,
	impl_items: ColumnBuilder<ImplItem>,
	trait_items: ColumnBuilder<TraitItem>,
	use_trees: ColumnBuilder<UseTree>,
	type_params: ColumnBuilder<TypeParam>,
	function_params: ColumnBuilder<FunctionParam>,
	struct_fields: ColumnBuilder<StructField>,
	enum_entries: ColumnBuilder<EnumEntry>,
	import_entries: ColumnBuilder<ImportEntry>,
	attributes: Vec<Attribute>,
	export_entries: Vec<ExportEntry>,
	paths: Vec<Path>,
}

impl AstBuilder {
	fn finish(self, root: List<Item>) -> AST {
		AST {
			root,
			types: self.types.finish(),
			consts: self.consts.finish(),
			bounds: self.bounds.finish(),
			patterns: self.patterns.finish(),
			exprs: self.exprs.finish(),
			stmts: self.stmts.finish(),
			blocks: self.blocks.finish(),
			qualified_roots: self.qualified_roots.into_boxed_slice(),
			segments: self.segments.into_boxed_slice(),
			type_args: self.type_args.into_boxed_slice(),
			type_lists: self.type_lists.into_boxed_slice(),
			bound_lists: self.bound_lists.into_boxed_slice(),
			assoc_bindings: self.assoc_bindings.into_boxed_slice(),
			function_type_params: self.function_type_params.into_boxed_slice(),
			pat_lists: self.pat_lists.into_boxed_slice(),
			pattern_elements: self.pattern_elements.into_boxed_slice(),
			pattern_fields: self.pattern_fields.into_boxed_slice(),
			expr_lists: self.expr_lists.into_boxed_slice(),
			stmt_lists: self.stmt_lists.into_boxed_slice(),
			named_arguments: self.named_arguments.into_boxed_slice(),
			arms: self.arms.into_boxed_slice(),
			items: self.items.finish(),
			impl_items: self.impl_items.finish(),
			trait_items: self.trait_items.finish(),
			use_trees: self.use_trees.finish(),
			type_params: self.type_params.finish(),
			function_params: self.function_params.finish(),
			struct_fields: self.struct_fields.finish(),
			enum_entries: self.enum_entries.finish(),
			import_entries: self.import_entries.finish(),
			attributes: self.attributes.into_boxed_slice(),
			export_entries: self.export_entries.into_boxed_slice(),
			paths: self.paths.into_boxed_slice(),
		}
	}

	fn push_type(&mut self, kind: TypeExpression, span: TextSpan) -> TypeId {
		TypeId::new(self.types.push(kind, span))
	}

	fn push_const(&mut self, kind: ConstArgument, span: TextSpan) -> ConstId {
		ConstId::new(self.consts.push(kind, span))
	}

	fn push_bound(&mut self, kind: BoundExpression, span: TextSpan) -> BoundId {
		BoundId::new(self.bounds.push(kind, span))
	}

	fn push_pattern(&mut self, kind: Pattern, span: TextSpan) -> PatId {
		PatId::new(self.patterns.push(kind, span))
	}

	fn push_expr(&mut self, kind: Expression, span: TextSpan) -> ExprId {
		ExprId::new(self.exprs.push(kind, span))
	}

	fn push_statement(&mut self, kind: Statement, span: TextSpan) -> StmtId {
		StmtId::new(self.stmts.push(kind, span))
	}

	fn push_block(&mut self, block: Block, span: TextSpan) -> BlockId {
		BlockId::new(self.blocks.push(block, span))
	}

	fn push_segment(&mut self, segment: PathSegment) -> SegmentId {
		let id = SegmentId::new(u32::try_from(self.segments.len()).unwrap());
		self.segments.push(segment);
		id
	}

	fn push_qualified_root(
		&mut self,
		root: QualifiedPathRoot,
	) -> QualifiedRootId {
		let id = QualifiedRootId::new(
			u32::try_from(self.qualified_roots.len()).unwrap(),
		);
		self.qualified_roots.push(root);
		id
	}

	/// Writes `items` as one list, contiguous: a list's items are all parsed
	/// before it is written, so a nested list never lands inside it.
	fn push_list<T: BuildVec>(
		&mut self,
		items: impl IntoIterator<Item = T>,
	) -> List<T> {
		let store = T::vec_mut(self);
		let start = u32::try_from(store.len()).unwrap();
		store.extend(items);
		let len = u32::try_from(store.len()).unwrap() - start;
		List {
			start,
			len,
			of: PhantomData,
		}
	}

	/// [`AstBuilder::push_list`], for nodes kept with their spans.
	fn push_nodes<T: BuildColumn>(
		&mut self,
		nodes: impl IntoIterator<Item = Spanned<T>>,
	) -> List<T> {
		let column = T::column_mut(self);
		let start = u32::try_from(column.kinds.len()).unwrap();
		for node in nodes {
			column.push(node.inner, node.span);
		}
		let len = u32::try_from(column.kinds.len()).unwrap() - start;
		List {
			start,
			len,
			of: PhantomData,
		}
	}

	/// One node of a column addressed on its own, outside any list (a
	/// `use` tree's rest).
	fn push_node<T: Identified + BuildColumn>(
		&mut self,
		node: T,
		span: TextSpan,
	) -> T::Id {
		T::id(T::column_mut(self).push(node, span))
	}
}

impl AST {
	pub fn ty(&self, id: TypeId) -> TypeExpression {
		self.types.kinds[usize::from(id)]
	}

	pub fn type_span(&self, id: TypeId) -> TextSpan {
		self.types.spans[usize::from(id)]
	}

	pub fn constant(&self, id: ConstId) -> ConstArgument {
		self.consts.kinds[usize::from(id)]
	}

	pub fn const_span(&self, id: ConstId) -> TextSpan {
		self.consts.spans[usize::from(id)]
	}

	pub fn bound(&self, id: BoundId) -> BoundExpression {
		self.bounds.kinds[usize::from(id)]
	}

	pub fn bound_span(&self, id: BoundId) -> TextSpan {
		self.bounds.spans[usize::from(id)]
	}

	pub fn pattern(&self, id: PatId) -> Pattern {
		self.patterns.kinds[usize::from(id)]
	}

	pub fn pattern_span(&self, id: PatId) -> TextSpan {
		self.patterns.spans[usize::from(id)]
	}

	/// The `mut` of a binding written with one, which the pattern starts
	/// at.
	pub fn pattern_mut_span(&self, id: PatId) -> Option<TextSpan> {
		match self.pattern(id) {
			Pattern::Binding { mutable: true, .. } => {
				let start = self.pattern_span(id).start;
				let len = Keyword::Mut.as_str().len() as u32;
				Some(TextSpan::new(start, start + len))
			}
			_ => None,
		}
	}

	pub fn expr(&self, id: ExprId) -> Expression {
		self.exprs.kinds[usize::from(id)]
	}

	pub fn expr_span(&self, id: ExprId) -> TextSpan {
		self.exprs.spans[usize::from(id)]
	}

	pub fn statement(&self, id: StmtId) -> Statement {
		self.stmts.kinds[usize::from(id)]
	}

	pub fn statement_span(&self, id: StmtId) -> TextSpan {
		self.stmts.spans[usize::from(id)]
	}

	pub fn block(&self, id: BlockId) -> Block {
		self.blocks.kinds[usize::from(id)]
	}

	/// A block's span, its braces; a block with none written (an `if`
	/// labelled by mistake, read as the block around it) spans its tail.
	pub fn block_span(&self, id: BlockId) -> TextSpan {
		self.blocks.spans[usize::from(id)]
	}

	pub fn segment(&self, id: SegmentId) -> PathSegment {
		self.segments[usize::from(id)]
	}

	/// Where a unary or binary expression's operator is written.
	pub fn operator_span(&self, id: ExprId) -> TextSpan {
		let (start, text) = match self.expr(id) {
			Expression::Unary { operator, .. } => {
				(self.expr_span(id).start, operator.as_str())
			}
			Expression::Binary {
				operator,
				operator_start,
				..
			} => (operator_start, operator.as_str()),
			_ => unreachable!("only an operator expression has an operator"),
		};
		TextSpan::new(start, start + text.len() as u32)
	}

	/// Where a call's arguments are written: from the `(` to the end of the
	/// call for a positional list, the braces of a named one.
	pub fn arguments_span(&self, id: ExprId) -> TextSpan {
		match self.expr(id) {
			Expression::Call { open, .. } => {
				TextSpan::new(open, self.expr_span(id).end)
			}
			Expression::NamedCall { braces, .. } => braces,
			_ => unreachable!("only a call has arguments"),
		}
	}

	pub fn qualified_root(&self, id: QualifiedRootId) -> QualifiedPathRoot {
		self.qualified_roots[usize::from(id)]
	}

	pub fn list<T: Listed>(&self, list: List<T>) -> &[T] {
		&T::store(self)[list.range()]
	}

	/// A list's items, each with its span.
	pub fn spanned<'a, T: InColumn + Copy + 'a>(
		&'a self,
		list: List<T>,
	) -> impl ExactSizeIterator<Item = Spanned<T>> + 'a {
		let range = list.range();
		T::store(self)[range.clone()]
			.iter()
			.zip(&T::spans(self)[range])
			.map(|(&inner, &span)| Spanned { inner, span })
	}

	/// The spans of a list's items, in the list's order.
	pub fn spans<T: InColumn>(&self, list: List<T>) -> &[TextSpan] {
		&T::spans(self)[list.range()]
	}

	/// A list's items by id.
	pub fn ids<T: Identified>(
		&self,
		list: List<T>,
	) -> impl ExactSizeIterator<Item = T::Id> + use<T> {
		(list.start..list.start + list.len).map(T::id)
	}

	pub fn item(&self, id: ItemId) -> Item {
		self.items.kinds[usize::from(id)]
	}

	pub fn item_span(&self, id: ItemId) -> TextSpan {
		self.items.spans[usize::from(id)]
	}

	pub fn impl_item(&self, id: ImplItemId) -> ImplItem {
		self.impl_items.kinds[usize::from(id)]
	}

	pub fn impl_item_span(&self, id: ImplItemId) -> TextSpan {
		self.impl_items.spans[usize::from(id)]
	}

	pub fn trait_item(&self, id: TraitItemId) -> TraitItem {
		self.trait_items.kinds[usize::from(id)]
	}

	pub fn trait_item_span(&self, id: TraitItemId) -> TextSpan {
		self.trait_items.spans[usize::from(id)]
	}

	pub fn use_tree(&self, id: UseTreeId) -> UseTree {
		self.use_trees.kinds[usize::from(id)]
	}

	pub fn use_tree_span(&self, id: UseTreeId) -> TextSpan {
		self.use_trees.spans[usize::from(id)]
	}

	pub fn type_argument_span(&self, argument: TypeArgument) -> TextSpan {
		match argument {
			TypeArgument::Type(ty) => self.type_span(ty),
			TypeArgument::Const(constant) => self.const_span(constant),
		}
	}

	/// The span of a non-empty path, from its first segment's name to its
	/// last's, not including trailing type arguments.
	pub fn path_span(segments: &[PathSegment]) -> TextSpan {
		TextSpan::new(
			segments.first().unwrap().ident.span.start,
			segments.last().unwrap().ident.span.end,
		)
	}
}
