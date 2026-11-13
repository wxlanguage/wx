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

impl CommentMap {
	pub fn empty() -> Self {
		Self(Box::new([]))
	}

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

/// Represents an item in a separated list, storing both the item and its
/// trailing separator.
///
/// Used for comma-separated lists like function parameters `(a, b, c)` or
/// statement sequences. The `separator` field holds the token that follows this
/// item (e.g., `,` or `;`), if present.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Separated<T> {
	pub inner: T,
	pub separator: Option<TextSpan>,
}

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
	/// `-{expr}`
	Unary {
		operator: Spanned<UnaryOp>,
		operand: Box<Spanned<Expression>>,
	},
	/// `{expr} + {expr}`
	Binary {
		left: Box<Spanned<Expression>>,
		operator: Spanned<BinaryOp>,
		right: Box<Spanned<Expression>>,
	},
	/// `{expr}::<...>(a, b)`: a function call, or the construction of a
	/// struct, by position. The arguments are spanned by their parentheses.
	Call {
		callee: Box<Spanned<Expression>>,
		arguments: Spanned<Box<[Separated<Spanned<Expression>>]>>,
	},
	/// `{expr}::<...>({ x: a, y })`: the same, naming each parameter (or
	/// field). The named list is the call's only argument, spanned by its
	/// braces.
	NamedCall {
		callee: Box<Spanned<Expression>>,
		arguments: Spanned<Box<[Separated<Spanned<NamedArgument>>]>>,
	},
	/// `{expr}.{method}::<...>(a, b)`
	MethodCall(Box<MethodCallExpr>),
	/// `{expr}.{method}::<...>({ x: a, y })`
	NamedMethodCall(Box<MethodCallExpr<NamedArgument>>),
	/// `{expr}.{member}`, or `{expr}.{member}::<...>`: the type arguments
	/// are only meaningful when a call follows, which makes it a
	/// `MethodCall`; the checker rejects them on a field.
	ObjectAccess {
		object: Box<Spanned<Expression>>,
		member: PathSegment,
	},
	/// `{expr}.*`
	Deref {
		pointer: Box<Spanned<Expression>>,
	},
	/// `{expr}.&` — always produces a shared reference.
	AddressOf {
		value: Box<Spanned<Expression>>,
	},
	/// `return {expr}`
	Return {
		value: Option<Box<Spanned<Expression>>>,
	},
	/// `block :label { ... }`, or a construct's own block (`if`, `loop`, a
	/// match arm, a function body), which has no label. The statements are
	/// spanned by their braces, which a keyword block's own span starts
	/// before.
	Block {
		label: Option<Spanned<SymbolU32>>,
		statements: Spanned<Box<[Separated<Spanned<Statement>>]>>,
	},
	/// `break (:{label})? {expr}?`
	Break {
		label: Option<Spanned<SymbolU32>>,
		value: Option<Box<Spanned<Expression>>>,
	},
	/// `if {expr} { ... }`
	IfElse {
		condition: Box<Spanned<Expression>>,
		then_block: Box<Spanned<Expression>>,
		else_block: Option<Box<Spanned<Expression>>>,
	},
	/// `match {expr} { {pattern} => { ... }, ... }`
	Match {
		scrutinee: Box<Spanned<Expression>>,
		arms: Box<[Separated<Spanned<MatchArm>>]>,
	},
	/// `continue (:{label})?`
	Continue {
		label: Option<Spanned<SymbolU32>>,
	},
	/// `loop :label { ... }`
	Loop {
		label: Option<Spanned<SymbolU32>>,
		block: Box<Spanned<Expression>>,
	},
	/// `_` — discard in value position (e.g. `_ = expr;`)
	Placeholder,
	/// Raw quoted string text is recovered from the expression span.
	String,
	/// 'a' — raw source text (including quotes) is recovered from span
	Char,
	/// A `::` separated path: `foo`, `module::Point`, `module::Point::<i32>`.
	/// Replaces bare `Identifier`, `NamespaceAccess`, and path-typed
	/// `TypeApplication` as the canonical representation for named references.
	Path(Box<[PathSegment]>),
	/// `<Type as Trait>::item` — a qualified path pinning down exactly
	/// which trait's item is meant. Composes with the usual postfix grammar
	/// (`Call`, `ObjectAccess`, `Index`) like any other primary expression,
	/// e.g. `<Type as Trait>::method(x)`.
	QualifiedPath {
		root: QualifiedRootId,
		segments: Box<[PathSegment]>,
	},
	/// `<Type>::item` — a bare bracketed type used as a path root, with no
	/// trait qualification. Distinct from `QualifiedPath`: this doesn't
	/// disambiguate anything (it resolves exactly like the unbracketed
	/// `Type::item` would), it's purely for self-types that can't be
	/// written as a plain path segment (e.g. `<[T]>::method()`).
	Grouped {
		inner: TypeId,
		segments: Box<[PathSegment]>,
	},
	/// `(a, b, c)`, `(a)`, `(a,)` or `()`: any parenthesized list, as
	/// written. One element is that element, which TIR unwraps.
	Tuple {
		elements: Box<[Separated<Spanned<Expression>>]>,
	},
	/// `value: Type`, an element of a parenthesized list (`(5: i32)`,
	/// `f(x: u8, y)`) checked against the type it is written with. It
	/// converts nothing.
	Ascription {
		value: Box<Spanned<Expression>>,
		ty: TypeId,
	},
	/// `[a, b, c]`
	ArrayList {
		elements: Box<[Separated<Spanned<Expression>>]>,
	},
	/// `[value; count]`; the count is a length, a literal or a constant.
	ArrayRepeat {
		value: Box<Spanned<Expression>>,
		count: ConstId,
	},
	/// `expr[index]`
	Index {
		object: Box<Spanned<Expression>>,
		index: Box<Spanned<Expression>>,
	},
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
/// A method call; `Argument` is `Expression` for one by position and
/// `NamedArgument` for one by name.
pub struct MethodCallExpr<Argument = Expression> {
	pub object: Box<Spanned<Expression>>,
	/// The method's name, with the type arguments written on it
	/// (`.m::<T>(..)`).
	pub method: PathSegment,
	/// Spanned by their delimiters: the parentheses of a list by position,
	/// the braces of one by name.
	pub arguments: Spanned<Box<[Separated<Spanned<Argument>>]>>,
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct NamedArgument {
	pub name: Spanned<SymbolU32>,
	/// `None` means shorthand: `{ name }` is equivalent to `{ name: name }`
	pub value: Option<Box<Spanned<Expression>>>,
}

/// One arm of a `match` expression: `{pattern} => { ... }` or
/// `{pattern} => expr`. The pattern
/// says what each of its terms is on its own: a name binds, a literal
/// compares with that value, a qualified path with that constant.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct MatchArm {
	pub pattern: Spanned<Pattern>,
	pub body: Box<Spanned<Expression>>,
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
/// `Point<i32>`. Its own type rather than a bare `Box<[PathSegment]>`
/// specifically so its span can be a real method: Rust doesn't allow an
/// inherent impl on `[PathSegment]` itself, only on a named local type, and
/// a stored `Spanned` wrapper around the box would just duplicate what
/// `span()` recomputes on demand from the segments themselves.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Path {
	pub segments: Box<[PathSegment]>,
}

impl Path {
	/// The span of the whole path, from its first segment's identifier to
	/// its last — not including any trailing generic arguments.
	pub fn span(&self) -> TextSpan {
		TextSpan::new(
			self.segments.first().unwrap().ident.span.start,
			self.segments.last().unwrap().ident.span.end,
		)
	}
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
		match self {
			Expression::Block { .. }
			| Expression::IfElse { .. }
			| Expression::Loop { .. }
			| Expression::Match { .. } => true,
			_ => false,
		}
	}

	#[inline]
	pub fn as_block_statements(&self) -> &[Separated<Spanned<Statement>>] {
		match self {
			Expression::Block { statements, .. } => &statements.inner,
			_ => unreachable!("expected a block expression"),
		}
	}
}

/// A generic parameter declaration: a type, `T` or `T: Bound1 + Bound2`, or
/// a constant, `const N: Type`.
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
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Pattern {
	/// `_`
	Wildcard,
	/// `[mut] name`
	Binding {
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
	},
	/// A constant, named by a path: `const MAX`, `Ordering::Less`,
	/// `Self::LIMIT`. A path of one segment can only be a constant the
	/// author marked with `const`; a longer one names a constant already.
	Constant {
		path: Box<[PathSegment]>,
	},
	/// `0`, `-1`, `'a'`
	Literal(Literal),
	/// `A | B | C`; each separator is a `|`.
	Or(Box<[Separated<Spanned<Pattern>>]>),
	Destructure(Destructure),
	/// A pattern the parser could not read: the diagnostic is already out,
	/// and nothing here can be checked.
	Error,
}

/// Destructuring; each of its children is a pattern of its own.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Destructure {
	/// `(a, .., z)`
	Tuple { elements: PatternElements },
	/// `Name(pat, ..)` or `module::Name(pat, ..)`, written exactly as its
	/// construction is (`Name(1, 2)`), so a pattern and a value read the same
	/// way.
	Struct {
		path: Box<[PathSegment]>,
		elements: PatternElements,
	},
	/// `Name({ field, other: pat, .. })`, as `Name({ x: 1, y: 2 })` constructs
	/// it.
	NamedStruct {
		path: Box<[PathSegment]>,
		fields: PatternFields,
	},
}

/// A positional list exactly as written: how many `..` there are and where
/// is a semantic question TIR answers, not a parse-time assumption.
pub type PatternElements = Box<[Separated<Spanned<PatternElement>>]>;

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum PatternElement {
	Pattern(Pattern),
	/// `..`
	Rest,
}

/// A named list exactly as written; see [`PatternElements`].
pub type PatternFields = Box<[Separated<Spanned<PatternFieldItem>>]>;

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum PatternFieldItem {
	Field(PatternField),
	/// `..`
	Rest,
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct PatternField {
	pub name: Spanned<SymbolU32>,
	/// `None` = shorthand `{ x }`: the field binds a local of its own name,
	/// the same as `{ x: x }`.
	pub pattern: Option<Spanned<Pattern>>,
}

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

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Statement {
	/// `{expr}`
	Expression(Box<Spanned<Expression>>),
	/// `local <pattern> [: type] = {expr}`
	LocalDefinition {
		pattern: Spanned<Pattern>,
		ty: Option<TypeId>,
		value: Box<Spanned<Expression>>,
	},
}

impl Statement {
	pub fn is_block_like(&self) -> bool {
		match self {
			Statement::Expression(expr) => expr.inner.is_block_like(),
			Statement::LocalDefinition { .. } => false,
		}
	}
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

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
/// A parameter, written like a struct field: `binding: Type`, or `Type`
/// alone, which binds nothing as `_: Type` does. The receiver is
/// `self: Type`.
pub struct FunctionParam {
	pub binding: Option<Binding>,
	pub ty: TypeId,
}

/// The payload of an attribute.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum AttributeValue {
	/// `#[inline]` — name only, no payload.
	Word,
	/// `#[memory_limits({ min_pages: 1, max_pages: 10 })]` — arguments by
	/// name, written as a call's (`f({ x: 1 })`). What each value may be is
	/// the attribute's to say, where it is resolved.
	Named(Box<[Separated<Spanned<NamedArgument>>]>),
}

/// A single attribute on an item, e.g. `#[inline]` or
/// `#[memory_limits({ min_pages: 1 })]`.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct Attribute {
	pub name: Spanned<SymbolU32>,
	pub value: AttributeValue,
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum ImplItem {
	/// A method or associated function — TIR distinguishes the two after
	/// parsing, by checking whether the first param is named `self`.
	Function {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		block: Box<Spanned<Expression>>,
	},
	Constant {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	AssocType {
		/// Always an error to have set — an associated type is only legal in
		/// a trait impl, where visibility comes from the trait. Recorded
		/// anyway so the qualifier can be reported and round-tripped:
		/// dropping it here made the formatter delete `pub` from the source.
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: TypeId,
		attributes: Box<[Attribute]>,
	},
}

impl ImplItem {
	pub fn is_block_like(&self) -> bool {
		match self {
			ImplItem::Function { .. } => true,
			ImplItem::Constant { .. } | ImplItem::AssocType { .. } => false,
		}
	}
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum TraitItem {
	/// A method with an optional default body.
	Function {
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		/// `None` = abstract (must be provided by impl); `Some` = default
		/// implementation.
		body: Option<Box<Spanned<Expression>>>,
	},
	/// An associated constant declaration, with an optional default value.
	/// `None` = abstract (must be provided by every impl); `Some` = a
	/// default value impls may omit and inherit as-is.
	Const {
		name: Spanned<SymbolU32>,
		attributes: Box<[Attribute]>,
		ty: TypeId,
		value: Option<Box<Spanned<Expression>>>,
	},
	/// An associated type declaration, optionally with a default value.
	AssociatedType {
		name: Spanned<SymbolU32>,
		attributes: Box<[Attribute]>,
		/// Trait bounds the concrete type must satisfy. `None` = unconstrained.
		bounds: Option<BoundId>,
		/// Used when an impl does not provide this associated type.
		value: Option<TypeId>,
	},
}

impl TraitItem {
	pub fn is_block_like(&self) -> bool {
		match self {
			TraitItem::Function { body, .. } => body.is_some(),
			TraitItem::Const { .. } | TraitItem::AssociatedType { .. } => false,
		}
	}
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct FunctionSignature {
	pub name: Spanned<SymbolU32>,
	/// Generic type parameters `<T, U: Bound>`. Empty = monomorphic.
	pub type_params: Box<[Spanned<TypeParam>]>,
	pub params: Box<[Separated<Spanned<FunctionParam>>]>,
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
		rest: Box<Spanned<UseTree>>,
	},
	/// `{ .. }` — several subtrees sharing the prefix walked to so far.
	/// `Separated<Spanned<_>>` is what `SeparatedGroup::parse` returns, and
	/// matches `ExportEntry`'s shape. Nothing reads the separator spans: a
	/// `use` group is formatted on one line, so it never emits a trailing
	/// comma the way a broken `export` block does.
	Group {
		segment: Spanned<SymbolU32>,
		branches: Spanned<Box<[Separated<Spanned<UseTree>>]>>,
	},
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct ExportEntry {
	pub name: Spanned<SymbolU32>,
	/// The span of the raw quoted external name.
	pub alias: Option<TextSpan>,
}

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
		tree: Spanned<UseTree>,
	},
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct EnumVariant {
	pub name: Spanned<SymbolU32>,
	pub value: Option<Box<Spanned<Expression>>>,
}

/// An entry of an enum body, as written.
#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum EnumEntry {
	Variant(EnumVariant),
	/// A `..`: the variants name some of the enum's values, and every value of
	/// its repr is valid. It is not a variant. Where it is written, and how
	/// many there are, is for the checker to judge.
	Rest,
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub enum Item {
	Function {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
		block: Box<Spanned<Expression>>,
	},
	FunctionDeclaration {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
	},
	/// A package contract member whose implementation is supplied externally.
	PackageFunction {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: Box<[Attribute]>,
		signature: FunctionSignature,
	},
	PackageConst {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		ty: TypeId,
	},
	PackageType {
		pub_span: Option<TextSpan>,
		crate_span: TextSpan,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		type_params: Box<[Spanned<TypeParam>]>,
	},
	Global {
		pub_span: Option<TextSpan>,
		mut_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	Export {
		entry: Spanned<ExportEntry>,
	},
	ExportBlock {
		/// Span of the `export` keyword.
		keyword_span: TextSpan,
		entries: Box<[Separated<Spanned<ExportEntry>>]>,
	},
	Import {
		external_name: TextSpan,
		internal_name: Spanned<SymbolU32>,
		items: Spanned<Box<[Separated<Spanned<ImportEntry>>]>>,
	},
	Enum {
		pub_span: Option<TextSpan>,
		repr: Option<TypeId>,
		name: Spanned<SymbolU32>,
		entries: Box<[Separated<Spanned<EnumEntry>>]>,
		attributes: Box<[Attribute]>,
	},
	/// `impl Type { ... }`
	InherentImpl {
		type_params: Box<[Spanned<TypeParam>]>,
		target: Path,
		items: Box<[Separated<Spanned<ImplItem>>]>,
	},
	/// `impl Trait for Type { ... }` / `impl<T> Trait for Type<T> { ... }`
	TraitImpl {
		type_params: Box<[Spanned<TypeParam>]>,
		/// Plain path to the trait, e.g. `module::Trait`.
		trait_name: Path,
		target: Path,
		items: Box<[Separated<Spanned<ImplItem>>]>,
	},
	/// `struct Point(x: i32, y: i32);`, `struct Pair(i32, i32);` — one form
	/// for every struct. A field's name is optional, field by field, like its
	/// `pub`; a struct is constructed by a call, by position always and by
	/// name when every field has one.
	Struct {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		type_params: Box<[Spanned<TypeParam>]>,
		fields: Box<[Separated<Spanned<StructField>>]>,
	},
	Memory {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		size: TypeId,
	},
	Const {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		ty: Option<TypeId>,
		value: Box<Spanned<Expression>>,
		attributes: Box<[Attribute]>,
	},
	Module {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		items: Spanned<Box<[Separated<Spanned<Item>>]>>,
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
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		/// Supertrait bounds: `trait X: Y + Z { ... }`.  `None` = no bounds.
		supertraits: Option<BoundId>,
		items: Box<[Separated<Spanned<TraitItem>>]>,
	},
	/// `typeset Name: A + B { T1, T2, ... }` — a closed compile-time set of
	/// concrete types. The optional bound clause after `:` applies to every
	/// member: each member must satisfy `A + B`, and a body generic over the
	/// typeset may rely on those bounds. `None` = no bounds required.
	TypeSet {
		pub_span: Option<TextSpan>,
		attributes: Box<[Attribute]>,
		name: Spanned<SymbolU32>,
		bounds: Option<BoundId>,
		/// `SeparatedGroup` always wraps each item in `Spanned<T>`; `Path`'s
		/// own `span()` makes that wrapper redundant here, but there's no
		/// avoiding it without changing `SeparatedGroup` itself.
		members: Box<[Separated<Spanned<Path>>]>,
	},
	/// `use math::add;`, `use math::*;`, `use math::{trig::sin, ops::*};` —
	/// brings names from another namespace into this one.
	Use {
		pub_span: Option<TextSpan>,
		tree: Spanned<UseTree>,
	},
	/// `type Name = TypeExpr;` or `type Name<T> = TypeExpr;` — a transparent
	/// alias. `body` is `None` only for a bodiless `#[intrinsic] type Name;`
	/// declaration (primitives).
	TypeAlias {
		pub_span: Option<TextSpan>,
		name: Spanned<SymbolU32>,
		type_params: Box<[Spanned<TypeParam>]>,
		body: Option<TypeId>,
		attributes: Box<[Attribute]>,
	},
}

#[cfg_attr(any(debug_assertions, test), derive(Debug, serde::Serialize))]
pub struct StructField {
	pub pub_span: Option<TextSpan>,
	/// `None` for a positional field: `struct Pair(i32, i32);`. A binding's
	/// `mut` is parsed; what it allows is not checked yet.
	pub binding: Option<Binding>,
	pub ty: TypeId,
}

impl Item {
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
	pub fn set_attributes(&mut self, attrs: Box<[Attribute]>) {
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
}

/// What an [`AST`] holds in a list, and which of its vectors holds it.
pub trait Listed: Sized {
	fn store(ast: &AST) -> &Vec<Self>;
	fn store_mut(ast: &mut AST) -> &mut Vec<Self>;
}

macro_rules! listed {
	($($item:ty => $field:ident),+ $(,)?) => {
		$(impl Listed for $item {
			fn store(ast: &AST) -> &Vec<Self> {
				&ast.$field
			}
			fn store_mut(ast: &mut AST) -> &mut Vec<Self> {
				&mut ast.$field
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
}

/// A column of nodes of one kind, each with its span; a node's id is its
/// position.
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
struct Column<K> {
	kinds: Vec<K>,
	spans: Vec<TextSpan>,
}

impl<K> Default for Column<K> {
	fn default() -> Self {
		Self {
			kinds: Vec::new(),
			spans: Vec::new(),
		}
	}
}

impl<K> Column<K> {
	fn push(&mut self, kind: K, span: TextSpan) -> u32 {
		let index = u32::try_from(self.kinds.len()).unwrap();
		self.kinds.push(kind);
		self.spans.push(span);
		index
	}
}

/// One file's syntax tree. Type syntax lives in columns addressed by id (a
/// child before its parent) and lists by [`List`]; items, expressions and
/// patterns are still a tree, holding those ids
/// (`notes/ast-arena-plan.md`).
#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
pub struct AST {
	pub file_id: FileId,
	pub diagnostics: Vec<Diagnostic<FileId>>,
	pub items: Vec<Separated<Spanned<Item>>>,
	#[cfg_attr(any(debug_assertions, test), serde(skip))]
	pub comments: CommentMap,
	types: Column<TypeExpression>,
	consts: Column<ConstArgument>,
	bounds: Column<BoundExpression>,
	qualified_roots: Vec<QualifiedPathRoot>,
	segments: Vec<PathSegment>,
	type_args: Vec<TypeArgument>,
	type_lists: Vec<TypeId>,
	bound_lists: Vec<BoundId>,
	assoc_bindings: Vec<AssocBinding>,
	function_type_params: Vec<FunctionTypeParam>,
}

impl AST {
	fn new(file_id: FileId) -> Self {
		Self {
			file_id,
			diagnostics: Vec::new(),
			items: Vec::new(),
			comments: CommentMap::empty(),
			types: Column::default(),
			consts: Column::default(),
			bounds: Column::default(),
			qualified_roots: Vec::new(),
			segments: Vec::new(),
			type_args: Vec::new(),
			type_lists: Vec::new(),
			bound_lists: Vec::new(),
			assoc_bindings: Vec::new(),
			function_type_params: Vec::new(),
		}
	}

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

	pub fn qualified_root(&self, id: QualifiedRootId) -> QualifiedPathRoot {
		self.qualified_roots[usize::from(id)]
	}

	pub fn list<T: Listed>(&self, list: List<T>) -> &[T] {
		&T::store(self)[list.start as usize..][..list.len as usize]
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

	fn push_type(&mut self, kind: TypeExpression, span: TextSpan) -> TypeId {
		TypeId::new(self.types.push(kind, span))
	}

	fn push_const(&mut self, kind: ConstArgument, span: TextSpan) -> ConstId {
		ConstId::new(self.consts.push(kind, span))
	}

	fn push_bound(&mut self, kind: BoundExpression, span: TextSpan) -> BoundId {
		BoundId::new(self.bounds.push(kind, span))
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
	fn push_list<T: Listed>(
		&mut self,
		items: impl IntoIterator<Item = T>,
	) -> List<T> {
		let store = T::store_mut(self);
		let start = u32::try_from(store.len()).unwrap();
		store.extend(items);
		let len = u32::try_from(store.len()).unwrap() - start;
		List {
			start,
			len,
			of: PhantomData,
		}
	}
}
