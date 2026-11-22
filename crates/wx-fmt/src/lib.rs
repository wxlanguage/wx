use std::num::NonZeroU32;

use string_interner::symbol::SymbolU32;
use wx_compiler::ast;
use wx_compiler::diagnostics::{TextOffset, TextSpan};
use wx_compiler::tir::unescape_string_literal;

#[cfg(test)]
mod tests;

/// A real arena node. The non-zero representation keeps `Option<NodeId>`
/// the same size as `NodeId`; absence is never represented by a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
struct NodeId(NonZeroU32);

impl NodeId {
	fn from_index(index: usize) -> Self {
		let index =
			u32::try_from(index).expect("formatting node arena exceeds u32");
		Self(
			index
				.checked_add(1)
				.and_then(NonZeroU32::new)
				.expect("formatting node arena exceeds u32"),
		)
	}

	fn index(self) -> usize {
		(self.0.get() - 1) as usize
	}
}

macro_rules! define_text {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $($variant:ident => $str:literal,)*
        }
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy)]
        $vis enum $name {
            $($variant,)*
        }

        impl $name {
            /// Every variant, in declaration order: `ALL[t as usize] == t`.
            const ALL: &'static [Self] = &[$(Self::$variant,)*];

            fn as_str(self) -> &'static str {
                match self {
                    $(Self::$variant => $str,)*
                }
            }
        }
    };
}

define_text! {
	enum Text {
		// keywords with trailing space
		Func    => "func ",
		Pub     => "pub ",
		Struct  => "struct ",
		Impl    => "impl",
		Trait   => "trait ",
		Module  => "mod ",
		Use     => "use ",
		Memory  => "memory ",
		Import  => "import ",
		Global  => "global ",
		Mut     => "mut ",
		Const   => "const ",
		TypeKw  => "type ",
		Typeset => "typeset ",
		Local   => "local ",
		Loop    => "loop ",
		If      => "if ",
		Match   => "match ",
		Enum    => "enum ",
		Export  => "export ",
		Package => "package ",
		Block   => "block ",
		// keywords without trailing space
		Break       => "break",
		Continue    => "continue",
		Return      => "return",
		// punctuation
		Semi             => ";",
		Comma            => ",",
		Dot              => ".",
		DotStar          => ".*",
		DotAmp           => ".&",
		DotDot           => "..",
		LBrace           => "{",
		RBrace           => "}",
		LParen           => "(",
		RParen           => ")",
		LBracket         => "[",
		RBracket         => "]",
		Lt               => "<",
		Gt               => ">",
		Star             => "*",
		Underscore       => "_",
		HashLBracket     => "#[",
		Colon            => ":",
		ColonColon       => "::",
		ColonColonLt     => "::<",
		ColonColonLBrace => "::{",
		// spaced punctuation / keywords
		Arrow            => " -> ",
		FatArrow         => " => ",
		As               => " as ",
		ColonSp          => ": ",
		CommaSp          => ", ",
		VbarSp           => " | ",
		PlusLead         => "+ ",
		EqSp             => " = ",
		EqBare           => " =",
		Else             => " else ",
		ForKw            => " for ",
		LabelColon       => " :",
		Space            => " ",
		SpaceLBrace      => " {",
		Where        => " where ",
		// compound tokens
		ExportLBrace => "export {",
		FuncParen    => "func(",
		// binary operators
		Add       => "+",
		Sub       => "-",
		Div       => "/",
		Rem       => "%",
		EqEq      => "==",
		NotEq     => "!=",
		LtEq      => "<=",
		GtEq      => ">=",
		AndAnd    => "&&",
		OrOr      => "||",
		Assign    => "=",
		AddAssign => "+=",
		SubAssign => "-=",
		MulAssign => "*=",
		DivAssign => "/=",
		RemAssign => "%=",
		Amp         => "&",
		Pipe        => "|",
		Caret       => "^",
		LtLt        => "<<",
		GtGt        => ">>",
		AmpAssign   => "&=",
		PipeAssign  => "|=",
		CaretAssign => "^=",
		LtLtAssign  => "<<=",
		GtGtAssign  => ">>=",
		// unary `!`, and the never type
		Bang => "!",
	}
}

impl From<ast::BinaryOp> for Text {
	fn from(op: ast::BinaryOp) -> Self {
		match op {
			ast::BinaryOp::Add => Text::Add,
			ast::BinaryOp::Sub => Text::Sub,
			ast::BinaryOp::Mul => Text::Star,
			ast::BinaryOp::Div => Text::Div,
			ast::BinaryOp::Rem => Text::Rem,
			ast::BinaryOp::Eq => Text::EqEq,
			ast::BinaryOp::NotEq => Text::NotEq,
			ast::BinaryOp::Less => Text::Lt,
			ast::BinaryOp::LessEq => Text::LtEq,
			ast::BinaryOp::Greater => Text::Gt,
			ast::BinaryOp::GreaterEq => Text::GtEq,
			ast::BinaryOp::And => Text::AndAnd,
			ast::BinaryOp::Or => Text::OrOr,
			ast::BinaryOp::Assign => Text::Assign,
			ast::BinaryOp::AddAssign => Text::AddAssign,
			ast::BinaryOp::SubAssign => Text::SubAssign,
			ast::BinaryOp::MulAssign => Text::MulAssign,
			ast::BinaryOp::DivAssign => Text::DivAssign,
			ast::BinaryOp::RemAssign => Text::RemAssign,
			ast::BinaryOp::BitAndAssign => Text::AmpAssign,
			ast::BinaryOp::BitOrAssign => Text::PipeAssign,
			ast::BinaryOp::BitXorAssign => Text::CaretAssign,
			ast::BinaryOp::LeftShiftAssign => Text::LtLtAssign,
			ast::BinaryOp::RightShiftAssign => Text::GtGtAssign,
			ast::BinaryOp::BitAnd => Text::Amp,
			ast::BinaryOp::BitOr => Text::Pipe,
			ast::BinaryOp::BitXor => Text::Caret,
			ast::BinaryOp::LeftShift => Text::LtLt,
			ast::BinaryOp::RightShift => Text::GtGt,
		}
	}
}

impl From<ast::UnaryOp> for Text {
	fn from(op: ast::UnaryOp) -> Self {
		match op {
			ast::UnaryOp::InvertSign => Text::Sub,
			ast::UnaryOp::Not => Text::Bang,
			ast::UnaryOp::BitNot => Text::Caret,
		}
	}
}

#[derive(Clone, Copy)]
enum Node {
	Text(Text),
	/// A slice of the original source addressed by span
	SourceText(TextSpan),
	/// An interned symbol resolved during rendering
	Symbol {
		symbol: SymbolU32,
		len: u32,
	},
	/// A possible line break, otherwise rendered as a space
	SoftLine,
	/// A possible line break, otherwise nothing
	Line,
	/// Always emit a newline followed by indentation, regardless of mode
	HardLine,
	/// Always emit a bare newline with no indentation — use to insert a blank line between items
	BlankLine,
	/// At least two nodes concatenated together; absent fragments are `None`.
	/// Children stored in `Arena::children[start .. start + len]`.
	Concat {
		start: u32,
		len: u32,
	},
	/// Owns the mode of its contents. Nested groups may independently
	/// become flat inside a broken parent.
	Group(NodeId),
	/// Increases the indentation level for all lines within this node
	Indent(NodeId),
	/// A fragment emitted only when the owning group is flat.
	IfFlat(NodeId),
	/// A fragment emitted only when the owning group is broken.
	IfBroken(NodeId),
	/// `fallback` flat if it fits on the current line; otherwise `body` flat
	/// on the next line, one indent deeper, if it fits there; otherwise
	/// `fallback` broken. `fallback`'s flat layout must be `body` inline.
	FlatBelow {
		body: NodeId,
		fallback: NodeId,
	},
}

/// Every node the builder makes, children of concatenations in a side list.
///
/// A fixed token or a line break carries nothing to tell two of them apart,
/// so each is made once, in `new`, and every use shares it. That is safe
/// because a node never changes once built, and the renderer decides
/// everything from its mode and indent, never from a node's identity.
struct Arena {
	nodes: Vec<Node>,
	children: Vec<NodeId>,
	/// Each token's node, indexed by `Text as usize`.
	texts: Box<[NodeId]>,
	soft_line: NodeId,
	line: NodeId,
	hard_line: NodeId,
	blank_line: NodeId,
	/// The trailing comma of a list that breaks.
	if_broken_comma: NodeId,
}

impl Arena {
	fn new() -> Self {
		let mut nodes = Vec::new();
		let mut shared = |node| {
			nodes.push(node);
			NodeId::from_index(nodes.len() - 1)
		};
		let texts: Box<[NodeId]> =
			Text::ALL.iter().map(|&t| shared(Node::Text(t))).collect();
		let soft_line = shared(Node::SoftLine);
		let line = shared(Node::Line);
		let hard_line = shared(Node::HardLine);
		let blank_line = shared(Node::BlankLine);
		let comma = texts[Text::Comma as usize];
		let if_broken_comma = shared(Node::IfBroken(comma));
		Self {
			nodes,
			children: Vec::new(),
			texts,
			soft_line,
			line,
			hard_line,
			blank_line,
			if_broken_comma,
		}
	}

	#[inline]
	fn alloc(&mut self, node: Node) -> NodeId {
		let id = self.nodes.len();
		self.nodes.push(node);
		NodeId::from_index(id)
	}

	/// A required document must contain at least one node. Optional
	/// fragments use `concat_optional` instead of allocating an empty node.
	fn concat(&mut self, children: &[NodeId]) -> NodeId {
		self.concat_optional(children)
			.expect("a required document must not be empty")
	}

	fn concat_optional(&mut self, children: &[NodeId]) -> Option<NodeId> {
		match *children {
			[] => None,
			[only] => Some(only),
			_ => {
				let start = self.children.len() as u32;
				let len = children.len() as u32;
				self.children.extend_from_slice(children);
				Some(self.alloc(Node::Concat { start, len }))
			}
		}
	}

	fn append(&mut self, first: NodeId, rest: Option<NodeId>) -> NodeId {
		match rest {
			Some(rest) => self.concat(&[first, rest]),
			None => first,
		}
	}

	fn prepend(&mut self, first: Option<NodeId>, rest: NodeId) -> NodeId {
		match first {
			Some(first) => self.concat(&[first, rest]),
			None => rest,
		}
	}

	#[inline]
	fn group(&mut self, inner: NodeId) -> NodeId {
		self.alloc(Node::Group(inner))
	}

	#[inline]
	fn indent(&mut self, inner: NodeId) -> NodeId {
		self.alloc(Node::Indent(inner))
	}
}

/// An entry of a block as written: a statement, or the tail after them.
#[derive(Clone, Copy)]
enum Entry {
	Statement(ast::StmtId),
	Tail(ast::ExprId),
}

struct Builder<'a> {
	interner: &'a ast::StringInterner,
	source: &'a str,
	/// The file's tree, where its type syntax is read by id.
	ast: &'a ast::AST,
	comments: &'a ast::CommentMap,
	arena: Arena,
}

/// What sits *before* a gap between comments and code. Decides whether the
/// first comment in the gap can trail the line, and what happens to blank
/// lines. "Entry" is whatever the list holds — item, statement, struct field,
/// enum variant, match arm, import or export entry.
#[derive(Clone, Copy)]
enum Before {
	/// The token that opens the list: `{`, or the keyword that precedes it.
	/// Nothing trails an opener — a comment written after `{` documents the
	/// body, not the line it sits on — and no blank line sits directly under
	/// one, because there is nothing above it for the blank to separate the
	/// body from.
	Opener { from: TextOffset },
	/// The end of an entry's content. A comment on that same line trails it,
	/// and a blank line the author left is kept.
	Entry { end: TextOffset },
	/// An entry that always stands apart from the next — a declaration that
	/// ends in `}`, or one followed by such a declaration. Like `Entry`, but a blank line goes in even where the
	/// author left none, even before the comments that close a list, so a
	/// list's last gap is always an `Entry`: there is nothing following for
	/// it to stand apart from.
	SpacedEntry { end: TextOffset },
	/// The end of an attribute. A comment on its line trails it, and no
	/// blank line separates it from what it is attached to.
	Attribute { end: TextOffset },
}

impl Before {
	/// The gap before an item of a list of declarations (a file, a `mod`, an
	/// impl or a trait body) that opens at `from`, given the item before it
	/// (its end, and whether it ended in `}`) and whether this one ends in
	/// `}`. An item that ends at its own `}` stands apart from its neighbours,
	/// however the author spaced them; between items that end in `;` the
	/// author's blank line is kept, as a grouping (a run of constants).
	fn declaration(
		from: TextOffset,
		previous: Option<(TextOffset, bool)>,
		ends_in_brace: bool,
	) -> Self {
		match previous {
			None => Before::Opener { from },
			Some((end, previous)) if previous || ends_in_brace => {
				Before::SpacedEntry { end }
			}
			Some((end, _)) => Before::Entry { end },
		}
	}
}

/// What sits *after* a gap. Decides only whether a line is opened once the
/// comments have been placed.
#[derive(Clone, Copy)]
enum After {
	/// Another entry begins at `start`. Its line is opened once the comments
	/// are placed, so an empty gap is just the line break and the caller can
	/// push the entry straight on.
	Entry { start: TextOffset },
	/// The list ends at `at` — a closing brace, or the end of the file. That
	/// bounds which comments belong to the gap and nothing more: no line is
	/// opened, because nothing follows.
	End { at: TextOffset },
}

/// What to do about a blank line at a break.
#[derive(Clone, Copy)]
enum Blank {
	/// Keep one if the author wrote one.
	Preserve,
	/// Put one in regardless.
	Force,
	/// Never put one in.
	Suppress,
}

/// How a delimited list is laid out.
#[derive(Clone, Copy)]
enum ListLayout {
	/// On one line when it fits, nothing inside the delimiters: `(x: i32)`.
	Tight,
	/// On one line when it fits, a space inside the delimiters: `{ u32, u64 }`.
	Padded,
	/// One entry per line, however short.
	Broken,
}

/// The grammar around an expression determines whether a singleton tuple
/// merely groups it. Keep operator grouping conservative; in particular,
/// a grouped field callee is not a method call.
#[derive(Clone, Copy)]
enum ExpressionPosition {
	Whole,
	ListElement,
	Operand,
	Callee,
	PostfixReceiver,
}

impl<'a> Builder<'a> {
	#[inline]
	fn text(&mut self, t: Text) -> NodeId {
		self.arena.texts[t as usize]
	}

	#[inline]
	fn hard_line(&mut self) -> NodeId {
		self.arena.hard_line
	}

	#[inline]
	fn soft_line(&mut self) -> NodeId {
		self.arena.soft_line
	}

	#[inline]
	fn line(&mut self) -> NodeId {
		self.arena.line
	}

	#[inline]
	fn blank_line(&mut self) -> NodeId {
		self.arena.blank_line
	}

	#[inline]
	fn if_break_comma(&mut self) -> NodeId {
		self.arena.if_broken_comma
	}

	#[inline]
	fn symbol(&mut self, symbol: SymbolU32) -> NodeId {
		let len = self.interner.resolve(symbol).unwrap().len() as u32;
		self.arena.alloc(Node::Symbol { symbol, len })
	}

	/// `block ` or `loop `, followed by `:label ` when there is one.
	fn labelled_keyword(
		&mut self,
		keyword: Text,
		label: Option<ast::Spanned<SymbolU32>>,
	) -> NodeId {
		let keyword = self.text(keyword);
		let Some(label) = label else {
			return keyword;
		};
		let colon = self.text(Text::Colon);
		let name = self.symbol(label.inner);
		let space = self.text(Text::Space);
		self.arena.concat(&[keyword, colon, name, space])
	}

	#[inline]
	fn source_text(&mut self, span: TextSpan) -> NodeId {
		self.arena.alloc(Node::SourceText(span))
	}

	/// Whether the author left a blank line between `from` and `to`.
	///
	/// Both ends of that region can hold code, so neither bound is the edge of
	/// a line. `from` is the end of an entry's *content*, and the separator
	/// the formatter emits itself (`;`, `,`) still follows it, so the rest of
	/// that line is skipped first. `to` is an item's `span.start`, which sits
	/// *after* its attributes — so what remains counts as a blank line only if
	/// it is whitespace all the way to a second newline. That is what keeps an
	/// `#[...]` line from reading as a blank one.
	fn has_blank_line(source: &str, from: usize, to: usize) -> bool {
		if to <= from {
			return false;
		}
		let between = &source[from..to];
		let Some(line_end) = between.find('\n') else {
			return false;
		};
		between[line_end + 1..]
			.chars()
			.take_while(|c| c.is_whitespace())
			.any(|c| c == '\n')
	}

	/// Splits the comments sitting in a gap into the one that trails the
	/// preceding code on its line, if any, and the ones that own the line they
	/// start.
	///
	/// This is the entire same-line-vs-own-line rule, and it is decided purely
	/// by what the author wrote: a comment trails iff nothing but horizontal
	/// space separates it from the end of the code before it. Line width never
	/// enters into it — the same rule rustfmt and Prettier use, because
	/// deciding by width would let a comment silently change which item it
	/// appears to document whenever an unrelated edit changed a line's length.
	///
	/// At most one comment can trail: a `//` comment runs to the end of its
	/// line, so every later comment in the gap necessarily has that newline in
	/// front of it. Only the first one is ever a candidate.
	///
	/// A doc comment is never trailing. `///` documents whatever follows it,
	/// so emitting one at the end of the previous line would reattach it to
	/// the wrong item. Neither is a comment with nothing but whitespace in
	/// front of it in the whole file — a header comment on line 1 has no code
	/// to trail, however little separates it from `prev_end`.
	fn split_trailing_comment(
		&self,
		prev_end: TextOffset,
		gap: &'a [ast::Comment],
	) -> (Option<&'a ast::Comment>, &'a [ast::Comment]) {
		match gap.split_first() {
			Some((first, rest))
				if first.kind != ast::CommentKind::Doc
					&& !self.source[usize::from(prev_end)
						..usize::from(first.span.start)]
						.contains('\n')
					&& !self.source[..usize::from(prev_end)]
						.trim_end()
						.is_empty() =>
			{
				(Some(first), rest)
			}
			_ => (None, gap),
		}
	}

	/// Opens the next line, with the blank line ahead of it decided by `blank`.
	fn push_line_break(
		&mut self,
		out: &mut Vec<NodeId>,
		from: TextOffset,
		to: TextOffset,
		blank: Blank,
	) {
		let wants_blank = match blank {
			Blank::Force => true,
			Blank::Suppress => false,
			Blank::Preserve => Self::has_blank_line(
				self.source,
				usize::from(from),
				usize::from(to),
			),
		};
		if wants_blank {
			out.push(self.blank_line());
		}
		out.push(self.hard_line());
	}

	/// Emits each comment on a line of its own, opening a line ahead of every
	/// one of them. `cursor` is where the preceding line's content ended, and
	/// `first` is the blank-line policy for the first break only — every later
	/// break keeps whatever the author left between the two comments.
	///
	/// Returns the end of the last comment emitted, or `cursor` unchanged if
	/// there were none, so the caller can measure its own break from there.
	fn push_own_line_comments(
		&mut self,
		out: &mut Vec<NodeId>,
		cursor: TextOffset,
		comments: &[ast::Comment],
		first: Blank,
	) -> TextOffset {
		let mut cursor = cursor;
		for (index, comment) in comments.iter().enumerate() {
			let blank = if index == 0 { first } else { Blank::Preserve };
			self.push_line_break(out, cursor, comment.span.start, blank);
			out.push(self.source_text(comment.span));
			cursor = comment.span.end;
		}
		cursor
	}

	/// Emits everything that goes between two pieces of code: the comment
	/// trailing the line, the comments owning a line of their own, the blank
	/// lines the author left, and the break that opens what comes next.
	///
	/// This is the only way comments reach the output, and the only way a list
	/// opens a line — so there is no such thing as a gap too empty to route
	/// through here. With no comments in it this is just the line break.
	///
	/// Every gap in every list is a combination of its two ends: an opener or
	/// an entry before it, an entry or the end of the list after it. A list's
	/// head gap, the gaps between its entries, the one before its closing
	/// brace, and the whole body of an empty `{ }` are that one operation with
	/// different ends — not four code paths, which is what let them drift
	/// apart. The division of labour: **what precedes the gap decides the
	/// blank line, what follows decides whether a line is opened.**
	///
	/// The caller must have pushed the preceding entry *and* its separator
	/// first, since a trailing comment goes after both.
	fn push_between(&mut self, out: &mut Vec<NodeId>, from: Before, to: After) {
		let hard_line = self.hard_line();
		self.push_between_breaking(out, from, to, hard_line);
	}

	/// `push_between`, opening the next entry with `gap_break` (a `SoftLine` or a
	/// `Line`, which a group may lay out flat) when the gap holds nothing:
	/// no comment and no blank line. A gap that holds something ends in a
	/// hard break as always, which keeps its group broken, so a list that
	/// collapses when it fits needs no check of its own for comments.
	/// Returns whether the gap held a comment.
	fn push_between_breaking(
		&mut self,
		out: &mut Vec<NodeId>,
		from: Before,
		to: After,
		gap_break: NodeId,
	) -> bool {
		let (start, first_blank, may_trail) = match from {
			Before::Opener { from } => (from, Blank::Suppress, false),
			Before::Entry { end } => (end, Blank::Preserve, true),
			Before::SpacedEntry { end } => (end, Blank::Force, true),
			Before::Attribute { end } => (end, Blank::Suppress, true),
		};
		let end = match to {
			After::Entry { start } => start,
			After::End { at } => at,
		};

		let gap = self.comments.between(start, end);
		let (trailing, own_line) = match may_trail {
			true => self.split_trailing_comment(start, gap),
			false => (None, gap),
		};

		if let Some(comment) = trailing {
			out.push(self.text(Text::Space));
			out.push(self.source_text(comment.span));
		}

		// Every break is measured from whatever ended the previous line, so a
		// blank line the author left before a comment survives just as one
		// left before the entry itself does.
		let cursor = trailing.map_or(start, |c| c.span.end);
		let cursor =
			self.push_own_line_comments(out, cursor, own_line, first_blank);

		if let After::Entry { start: next } = to {
			// `first_blank` belongs to the first break in the gap, wherever
			// that landed. If a comment already took it, this break is an
			// ordinary one.
			let blank = match own_line.is_empty() {
				true => first_blank,
				false => Blank::Preserve,
			};
			let wants_blank = match blank {
				Blank::Force => true,
				Blank::Suppress => false,
				Blank::Preserve => Self::has_blank_line(
					self.source,
					usize::from(cursor),
					usize::from(next),
				),
			};
			if trailing.is_none() && own_line.is_empty() && !wants_blank {
				out.push(gap_break);
			} else {
				self.push_line_break(out, cursor, next, blank);
			}
		}
		trailing.is_some() || !own_line.is_empty()
	}

	fn build(&mut self, ast: &ast::AST) -> Option<NodeId> {
		self.build_item_list(
			ast.root,
			TextSpan::from(0..self.source.len() as u32),
		)
	}

	/// `span` bounds the region the items live in — the whole file, or a `mod`
	/// body. Comments before the first item and after the last one belong to
	/// the list too, so both ends of `span` matter.
	fn build_item_list(
		&mut self,
		items: ast::List<ast::Item>,
		span: TextSpan,
	) -> Option<NodeId> {
		let ast = self.ast;
		let mut nodes: Vec<NodeId> = Vec::new();
		// The item before, and whether it ended in `}`. Before the first, the
		// opener is the file header or the line opening a `mod` body; at the
		// top of a file the break it emits has nothing in front of it and
		// disappears.
		let mut previous: Option<(TextOffset, bool)> = None;
		for item in ast.spanned(items) {
			let ends_in_brace = item.inner.ends_in_brace();
			let attributes = item.inner.attributes();
			self.push_between(
				&mut nodes,
				Before::declaration(span.start, previous, ends_in_brace),
				After::Entry {
					start: self.entry_start(attributes, item.span),
				},
			);
			self.build_attributes(&mut nodes, attributes, item.span.start);
			nodes.push(self.build_item(&item.inner, item.span));
			previous = Some((item.span.end, ends_in_brace));
		}
		// Comments after the last item, before the closing `}` or the end of
		// the file: all of them, in a header-only file or a `mod` body with
		// something to say and nothing to declare. The first may still trail
		// the last item's line.
		let before = match previous {
			None => Before::Opener { from: span.start },
			Some((end, _)) => Before::Entry { end },
		};
		self.push_between(&mut nodes, before, After::End { at: span.end });
		self.arena.concat_optional(&nodes)
	}

	fn build_item(&mut self, item: &ast::Item, span: TextSpan) -> NodeId {
		match item {
			ast::Item::Function {
				signature,
				block,
				pub_at,
				..
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut items, *signature);
				items.push(self.text(Text::Space));
				let body = self.build_fn_body(*block);
				items.push(body);
				let concat = self.arena.concat(&items);
				self.arena.group(concat)
			}
			ast::Item::FunctionDeclaration {
				pub_at, signature, ..
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut items, *signature);
				items.push(self.text(Text::Semi));
				self.arena.concat(&items)
			}
			ast::Item::PackageFunction {
				pub_at, signature, ..
			} => {
				let mut items = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Package));
				self.build_function_signature(&mut items, *signature);
				items.push(self.text(Text::Semi));
				self.arena.concat(&items)
			}
			ast::Item::PackageConst {
				pub_at, name, ty, ..
			} => {
				let mut items = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Package));
				items.push(self.text(Text::Const));
				items.push(self.symbol(name.inner));
				items.push(self.text(Text::ColonSp));
				items.push(self.build_type_expression(*ty));
				items.push(self.text(Text::Semi));
				self.arena.concat(&items)
			}
			ast::Item::PackageType {
				pub_at,
				name,
				type_params,
				type_params_span,
				..
			} => {
				let mut items = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Package));
				items.push(self.text(Text::TypeKw));
				items.push(self.symbol(name.inner));
				items.extend(
					self.build_type_params(*type_params, *type_params_span),
				);
				items.push(self.text(Text::Semi));
				self.arena.concat(&items)
			}
			ast::Item::Global {
				pub_at,
				mut_at,
				name,
				ty: type_annotation,
				value,
				..
			} => self.build_global_definition(
				*pub_at,
				*mut_at,
				name,
				*type_annotation,
				*value,
			),
			ast::Item::Export { entry } => {
				let mut parts: Vec<NodeId> = vec![self.text(Text::Export)];
				parts.push(self.build_export_entry(entry));
				parts.push(self.text(Text::Semi));
				self.arena.concat(&parts)
			}
			ast::Item::ExportBlock { entries, .. } => {
				self.build_export_definition(span, *entries)
			}
			ast::Item::Import {
				external_name,
				internal_name,
				entries,
				..
			} => self.build_import_definition(
				span,
				external_name,
				Some(internal_name),
				*entries,
			),
			ast::Item::Memory {
				pub_at, name, size, ..
			} => {
				let mut parts: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					parts.push(self.text(Text::Pub));
				}
				parts.push(self.text(Text::Memory));
				parts.push(self.symbol(name.inner));
				parts.push(self.text(Text::ColonSp));
				parts.push(self.build_type_expression(*size));
				parts.push(self.text(Text::Semi));
				self.arena.concat(&parts)
			}
			ast::Item::Enum {
				pub_at,
				repr,
				name,
				variants,
				..
			} => self
				.build_enum_definition(span, *pub_at, *repr, name, *variants),
			ast::Item::InherentImpl {
				type_params,
				type_params_span,
				target,
				items,
			} => {
				let type_params =
					self.build_type_params(*type_params, *type_params_span);
				self.build_impl_definition(span, type_params, target, *items)
			}
			ast::Item::TraitImpl {
				type_params,
				type_params_span,
				trait_name,
				target,
				items,
			} => {
				let type_params =
					self.build_type_params(*type_params, *type_params_span);
				self.build_impl_trait_definition(
					span,
					type_params,
					trait_name,
					target,
					*items,
				)
			}
			ast::Item::Const {
				pub_at,
				name,
				ty,
				value,
				..
			} => self.build_const_definition(*pub_at, name, *ty, *value),
			ast::Item::Module {
				pub_at,
				name,
				items,
				..
			} => self.build_module_definition(span, *pub_at, name, *items),
			ast::Item::ModuleDeclaration { pub_at, name } => {
				self.build_module_declaration(*pub_at, name)
			}
			ast::Item::Trait {
				pub_at,
				name,
				supertraits,
				items,
				..
			} => self.build_trait_definition(
				span,
				*pub_at,
				name,
				*supertraits,
				*items,
			),
			ast::Item::Struct {
				name,
				type_params,
				type_params_span,
				fields,
				pub_at,
				..
			} => {
				let type_params =
					self.build_type_params(*type_params, *type_params_span);
				self.build_struct_declaration(
					span,
					name,
					type_params,
					*fields,
					*pub_at,
				)
			}
			ast::Item::TypeSet {
				pub_at,
				name,
				bounds,
				members,
				..
			} => self.build_typeset_definition(
				span, *pub_at, name, *bounds, *members,
			),
			ast::Item::TypeAlias {
				pub_at,
				name,
				type_params,
				type_params_span,
				body,
				..
			} => {
				let type_params =
					self.build_type_params(*type_params, *type_params_span);
				self.build_type_alias_definition(
					*pub_at,
					name,
					type_params,
					*body,
				)
			}
			ast::Item::PackageInstance {
				pub_at,
				package,
				alias,
			} => {
				let mut parts: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					parts.push(self.text(Text::Pub));
				}
				parts.push(self.text(Text::Package));
				parts.push(self.source_text(*package));
				parts.push(self.text(Text::As));
				parts.push(self.symbol(alias.inner));
				parts.push(self.text(Text::Semi));
				self.arena.concat(&parts)
			}
			ast::Item::Use { tree, pub_at } => {
				let mut items: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Use));
				let tree = self.build_use_tree(self.ast.use_tree(*tree));
				items.push(tree);
				items.push(self.text(Text::Semi));
				self.arena.concat(&items)
			}
		}
	}

	/// A `use` tree, rendered on one line. Groups stay inline rather than
	/// breaking like an `export` block does: a `use` names things that live
	/// elsewhere, so its length tracks the path being imported rather than
	/// the size of anything in this file, and it stays short in practice.
	fn build_use_tree(&mut self, tree: ast::UseTree) -> NodeId {
		match tree {
			ast::UseTree::Glob { segment } => {
				let segment = self.symbol(segment.inner);
				let colons = self.text(Text::ColonColon);
				let star = self.text(Text::Star);
				self.arena.concat(&[segment, colons, star])
			}
			ast::UseTree::Name {
				segment: name,
				alias,
				..
			} => {
				let mut items: Vec<NodeId> = vec![self.symbol(name.inner)];
				if let Some(alias) = alias {
					items.push(self.text(Text::As));
					items.push(self.symbol(alias.inner));
				}
				self.arena.concat(&items)
			}
			ast::UseTree::Path { segment, rest } => {
				let segment = self.symbol(segment.inner);
				let colons = self.text(Text::ColonColon);
				let rest = self.build_use_tree(self.ast.use_tree(rest));
				self.arena.concat(&[segment, colons, rest])
			}
			ast::UseTree::Group {
				segment, branches, ..
			} => {
				let mut items: Vec<NodeId> = vec![
					self.symbol(segment.inner),
					self.text(Text::ColonColonLBrace),
				];
				for (index, &element) in
					self.ast.list(branches).iter().enumerate()
				{
					if index > 0 {
						items.push(self.text(Text::CommaSp));
					}
					let element = self.build_use_tree(element);
					items.push(element);
				}
				items.push(self.text(Text::RBrace));
				self.arena.concat(&items)
			}
		}
	}

	fn build_import_definition(
		&mut self,
		span: TextSpan,
		module: &TextSpan,
		alias: Option<&ast::Spanned<SymbolU32>>,
		entries: ast::List<ast::ImportEntry>,
	) -> NodeId {
		let ast = self.ast;
		let mut items: Vec<NodeId> =
			vec![self.text(Text::Import), self.source_text(*module)];

		if let Some(alias) = alias {
			items.push(self.text(Text::As));
			items.push(self.symbol(alias.inner));
		}

		items.push(self.text(Text::SpaceLBrace));

		if entries.is_empty() {
			self.build_empty_braced_comments(&mut items, span);
		} else {
			let mut entry_items: Vec<NodeId> = Vec::new();
			let mut before = Before::Opener { from: span.start };
			for entry in ast.spanned(entries) {
				self.push_between(
					&mut entry_items,
					before,
					After::Entry {
						start: entry.span.start,
					},
				);
				before = Before::Entry {
					end: entry.span.end,
				};

				let mut entry_nodes: Vec<NodeId> = Vec::new();

				match &entry.inner {
					ast::ImportEntry::Use { tree, pub_at } => {
						if pub_at.is_some() {
							entry_nodes.push(self.text(Text::Pub));
						}
						entry_nodes.push(self.text(Text::Use));
						entry_nodes.push(
							self.build_use_tree(self.ast.use_tree(*tree)),
						);
					}
					ast::ImportEntry::Declaration {
						external_name,
						declaration,
					} => {
						// A field that is the entry's own name says nothing
						// (`"log": func log(..)`), so it is dropped.
						let name = match declaration {
							ast::ImportDeclaration::Function {
								signature,
								..
							} => self.ast.signature(*signature).name.inner,
							ast::ImportDeclaration::Global { name, .. }
							| ast::ImportDeclaration::Memory { name, .. } => name.inner,
						};
						// Compared as decoded, so any spelling of the name
						// is its own; one that does not decode stays.
						if let Some(field) = external_name
							&& unescape_string_literal(
								field.extract_str(self.source),
							)
							.ok()
							.as_deref()
								!= self.interner.resolve(name)
						{
							entry_nodes.push(self.source_text(*field));
							entry_nodes.push(self.text(Text::ColonSp));
						}
						match declaration {
							ast::ImportDeclaration::Function {
								signature,
								..
							} => {
								self.build_function_signature(
									&mut entry_nodes,
									*signature,
								);
								let concat = self.arena.concat(&entry_nodes);
								let group = self.arena.group(concat);
								entry_nodes = vec![group];
							}
							ast::ImportDeclaration::Global {
								mut_at,
								name,
								ty,
								..
							} => {
								entry_nodes.push(self.text(Text::Global));
								if mut_at.is_some() {
									entry_nodes.push(self.text(Text::Mut));
								}
								entry_nodes.push(self.symbol(name.inner));
								entry_nodes.push(self.text(Text::ColonSp));
								entry_nodes
									.push(self.build_type_expression(*ty));
							}
							ast::ImportDeclaration::Memory { name, size } => {
								entry_nodes.push(self.text(Text::Memory));
								entry_nodes.push(self.symbol(name.inner));
								entry_nodes.push(self.text(Text::ColonSp));
								entry_nodes
									.push(self.build_type_expression(*size));
							}
						}
					}
				}

				// Every entry ends with a `;`, the last one included.
				entry_nodes.push(self.text(Text::Semi));

				let entry_concat = self.arena.concat(&entry_nodes);
				entry_items.push(entry_concat);
			}

			self.push_between(
				&mut entry_items,
				before,
				After::End { at: span.end },
			);

			let concat = self.arena.concat(&entry_items);
			let indented = self.arena.indent(concat);
			items.push(indented);
			items.push(self.line());
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(&items)
	}

	fn build_module_definition(
		&mut self,
		span: TextSpan,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		items: ast::List<ast::Item>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Module));
		nodes.push(self.symbol(name.inner));
		nodes.push(self.text(Text::SpaceLBrace));

		if let Some(body) = self.build_item_list(items, span) {
			// The body opens its own line: the gap before its first item is
			// where a comment written after `mod name {` belongs.
			nodes.push(self.arena.indent(body));
			nodes.push(self.hard_line());
		}

		nodes.push(self.text(Text::RBrace));
		let concat = self.arena.concat(&nodes);
		self.arena.group(concat)
	}

	fn build_module_declaration(
		&mut self,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Module));
		nodes.push(self.symbol(name.inner));
		nodes.push(self.text(Text::Semi));
		self.arena.concat(&nodes)
	}

	fn build_impl_definition(
		&mut self,
		span: TextSpan,
		type_params: Option<NodeId>,
		target: &ast::Path,
		items: ast::List<ast::ImplItem>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = vec![self.text(Text::Impl)];
		nodes.extend(type_params);
		nodes.push(self.text(Text::Space));
		nodes.push(self.build_type_path(self.ast.list(target.segments)));
		nodes.push(self.text(Text::SpaceLBrace));

		if !items.is_empty() {
			// The body opens its own line, so a comment after `{` trails it.
			let body = self.build_impl_item_list(span, items);
			nodes.push(self.arena.indent(body));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		let concat = self.arena.concat(&nodes);
		self.arena.group(concat)
	}

	fn build_impl_trait_definition(
		&mut self,
		span: TextSpan,
		type_params: Option<NodeId>,
		trait_name: &ast::Path,
		target: &ast::Path,
		items: ast::List<ast::ImplItem>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = vec![self.text(Text::Impl)];
		nodes.extend(type_params);
		nodes.push(self.text(Text::Space));
		let trait_id = self.build_type_path(self.ast.list(trait_name.segments));
		let for_kw = self.text(Text::ForKw);
		let target_id = self.build_type_path(self.ast.list(target.segments));
		let brace = self.text(Text::SpaceLBrace);
		nodes.extend([trait_id, for_kw, target_id, brace]);

		if !items.is_empty() {
			// The body opens its own line, so a comment after `{` trails it.
			let body = self.build_impl_item_list(span, items);
			nodes.push(self.arena.indent(body));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		let concat = self.arena.concat(&nodes);
		self.arena.group(concat)
	}

	fn build_impl_item_list(
		&mut self,
		span: TextSpan,
		items: ast::List<ast::ImplItem>,
	) -> NodeId {
		let ast = self.ast;
		let mut nodes: Vec<NodeId> = Vec::new();
		let mut previous: Option<(TextOffset, bool)> = None;
		for item in ast.spanned(items) {
			let ends_in_brace = item.inner.ends_in_brace();
			let attributes = item.inner.attributes();
			self.push_between(
				&mut nodes,
				Before::declaration(span.start, previous, ends_in_brace),
				After::Entry {
					start: self.entry_start(attributes, item.span),
				},
			);
			self.build_attributes(&mut nodes, attributes, item.span.start);
			nodes.push(self.build_impl_item(&item.inner));
			previous = Some((item.span.end, ends_in_brace));
		}
		self.push_between(
			&mut nodes,
			match previous {
				None => Before::Opener { from: span.start },
				Some((end, _)) => Before::Entry { end },
			},
			After::End { at: span.end },
		);
		self.arena.concat(&nodes)
	}

	fn build_impl_item(&mut self, item: &ast::ImplItem) -> NodeId {
		match item {
			ast::ImplItem::Function {
				pub_at,
				signature,
				block,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut nodes, *signature);
				nodes.push(self.text(Text::Space));
				nodes.push(self.build_fn_body(*block));
				let concat = self.arena.concat(&nodes);
				self.arena.group(concat)
			}
			ast::ImplItem::Constant {
				pub_at,
				name,
				ty,
				value,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				nodes.push(self.text(Text::Const));
				nodes.push(self.symbol(name.inner));
				if let Some(ty) = ty {
					nodes.push(self.text(Text::ColonSp));
					nodes.push(self.build_type_expression(*ty));
				}
				nodes.push(self.text(Text::EqSp));
				nodes.push(self.build_expression(*value));
				nodes.push(self.text(Text::Semi));
				self.arena.concat(&nodes)
			}
			ast::ImplItem::AssocType {
				pub_at, name, ty, ..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				if pub_at.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				nodes.push(self.text(Text::TypeKw));
				nodes.push(self.symbol(name.inner));
				nodes.push(self.text(Text::EqSp));
				nodes.push(self.build_type_expression(*ty));
				nodes.push(self.text(Text::Semi));
				self.arena.concat(&nodes)
			}
		}
	}

	fn build_trait_definition(
		&mut self,
		span: TextSpan,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		supertraits: Option<ast::BoundId>,
		items: ast::List<ast::TraitItem>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Trait));
		nodes.push(self.symbol(name.inner));

		if let Some(spanned) = supertraits {
			nodes.push(self.text(Text::ColonSp));
			nodes.push(self.build_bound_expression(spanned));
		}

		nodes.push(self.text(Text::SpaceLBrace));

		if !items.is_empty() {
			// The body opens its own line, so a comment after `{` trails it.
			let body = self.build_trait_item_list(span, items);
			nodes.push(self.arena.indent(body));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		let concat = self.arena.concat(&nodes);
		self.arena.group(concat)
	}

	fn build_trait_item_list(
		&mut self,
		span: TextSpan,
		items: ast::List<ast::TraitItem>,
	) -> NodeId {
		let ast = self.ast;
		let mut nodes: Vec<NodeId> = Vec::new();
		let mut previous: Option<(TextOffset, bool)> = None;
		for item in ast.spanned(items) {
			let ends_in_brace = item.inner.ends_in_brace();
			let attributes = item.inner.attributes();
			self.push_between(
				&mut nodes,
				Before::declaration(span.start, previous, ends_in_brace),
				After::Entry {
					start: self.entry_start(attributes, item.span),
				},
			);
			self.build_attributes(&mut nodes, attributes, item.span.start);
			nodes.push(self.build_trait_item(&item.inner));
			previous = Some((item.span.end, ends_in_brace));
		}
		self.push_between(
			&mut nodes,
			match previous {
				None => Before::Opener { from: span.start },
				Some((end, _)) => Before::Entry { end },
			},
			After::End { at: span.end },
		);
		self.arena.concat(&nodes)
	}

	fn build_trait_item(&mut self, item: &ast::TraitItem) -> NodeId {
		match item {
			ast::TraitItem::Function {
				signature, body, ..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				self.build_function_signature(&mut nodes, *signature);
				match body {
					Some(body) => {
						nodes.push(self.text(Text::Space));
						nodes.push(self.build_fn_body(*body));
						let concat = self.arena.concat(&nodes);
						self.arena.group(concat)
					}
					None => {
						nodes.push(self.text(Text::Semi));
						self.arena.concat(&nodes)
					}
				}
			}
			ast::TraitItem::Const {
				name, ty, value, ..
			} => {
				let mut nodes = vec![
					self.text(Text::Const),
					self.symbol(name.inner),
					self.text(Text::ColonSp),
					self.build_type_expression(*ty),
				];
				if let Some(value) = *value {
					nodes.push(self.text(Text::EqSp));
					nodes.push(self.build_expression(value));
				}
				nodes.push(self.text(Text::Semi));
				self.arena.concat(&nodes)
			}
			ast::TraitItem::AssociatedType {
				name,
				bounds,
				value,
				..
			} => {
				let mut nodes =
					vec![self.text(Text::TypeKw), self.symbol(name.inner)];
				if let Some(b) = bounds {
					nodes.push(self.text(Text::ColonSp));
					nodes.push(self.build_bound_expression(*b));
				}
				if let Some(value) = value {
					nodes.push(self.text(Text::EqSp));
					nodes.push(self.build_type_expression(*value));
				}
				nodes.push(self.text(Text::Semi));
				self.arena.concat(&nodes)
			}
		}
	}

	fn build_const_definition(
		&mut self,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		ty: Option<ast::TypeId>,
		value: ast::ExprId,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Const));
		nodes.push(self.symbol(name.inner));
		if let Some(ty) = ty {
			nodes.push(self.text(Text::ColonSp));
			nodes.push(self.build_type_expression(ty));
		}
		nodes.push(self.text(Text::EqSp));
		nodes.push(self.build_expression(value));
		nodes.push(self.text(Text::Semi));
		self.arena.concat(&nodes)
	}

	fn build_type_alias_definition(
		&mut self,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		type_params: Option<NodeId>,
		body: Option<ast::TypeId>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::TypeKw));
		nodes.push(self.symbol(name.inner));
		nodes.extend(type_params);
		if let Some(body) = body {
			nodes.push(self.text(Text::EqSp));
			nodes.push(self.build_type_expression(body));
		}
		nodes.push(self.text(Text::Semi));
		self.arena.concat(&nodes)
	}

	fn build_match_expression(
		&mut self,
		span: TextSpan,
		scrutinee: ast::ExprId,
		arms: &[ast::MatchArm],
	) -> NodeId {
		let ast = self.ast;
		let arm_span = |arm: &ast::MatchArm| {
			TextSpan::new(
				ast.pattern_span(arm.pattern).start,
				ast.branch_span(arm.body).end,
			)
		};
		let match_kw = self.text(Text::Match);
		let scrutinee_id = self.build_subject(scrutinee);
		let mut nodes: Vec<NodeId> =
			vec![match_kw, scrutinee_id, self.text(Text::SpaceLBrace)];

		if !arms.is_empty() {
			let mut arm_items: Vec<NodeId> = Vec::new();
			let mut before = Before::Opener { from: span.start };
			for (index, arm) in arms.iter().enumerate() {
				self.push_between(
					&mut arm_items,
					before,
					After::Entry {
						start: arm_span(arm).start,
					},
				);
				before = Before::Entry {
					end: arm_span(arm).end,
				};
				let mut an: Vec<NodeId> = Vec::new();
				self.build_pattern(&mut an, arm.pattern);
				an.push(self.text(Text::FatArrow));
				// A written `block` keeps its keyword (and label): it is the
				// arm's expression, and a `break` in it leaves it.
				let body = match arm.body {
					ast::Branch::Block(block) => {
						self.build_block_content(block, ast.block_span(block))
					}
					ast::Branch::Expression(expr) => {
						self.build_expression(expr)
					}
				};
				an.push(self.arena.group(body));
				if index + 1 < arms.len() {
					an.push(self.text(Text::Comma));
				} else {
					an.push(self.if_break_comma());
				}
				arm_items.push(self.arena.concat(&an));
			}
			self.push_between(
				&mut arm_items,
				before,
				After::End { at: span.end },
			);

			let concat = self.arena.concat(&arm_items);
			nodes.push(self.arena.indent(concat));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		self.arena.concat(&nodes)
	}

	fn build_enum_definition(
		&mut self,
		span: TextSpan,
		pub_at: Option<TextOffset>,
		repr: ast::List<ast::StructField>,
		name: &ast::Spanned<SymbolU32>,
		variants: ast::List<ast::EnumVariant>,
	) -> NodeId {
		let ast = self.ast;
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Enum));
		nodes.push(self.symbol(name.inner));
		// The repr is printed as a struct's fields are.
		if !repr.is_empty() {
			// The parentheses' own span is not kept: the list runs from the
			// name to its last field, and a comment after that is the body's.
			let entries = self.build_struct_fields(repr);
			let end =
				entries.last().map_or(name.span.end, |(span, _)| span.end);
			nodes.push(self.build_delimited_list(
				TextSpan::new(name.span.end, end),
				Text::LParen,
				Text::RParen,
				ListLayout::Tight,
				entries,
			));
		}
		nodes.push(self.text(Text::SpaceLBrace));

		if !variants.is_empty() {
			let mut entry_items: Vec<NodeId> = Vec::new();
			let mut before = Before::Opener { from: span.start };
			for (index, variant) in ast.spanned(variants).enumerate() {
				self.push_between(
					&mut entry_items,
					before,
					After::Entry {
						start: variant.span.start,
					},
				);
				before = Before::Entry {
					end: variant.span.end,
				};
				let mut en: Vec<NodeId> = Vec::new();
				en.push(self.symbol(variant.inner.name.inner));
				if let Some(value) = variant.inner.value {
					en.push(self.text(Text::EqSp));
					en.push(self.build_expression(value));
				}
				// Variants are separated by commas, and the last takes one when
				// the body breaks.
				if index + 1 < variants.len() {
					en.push(self.text(Text::Comma));
				} else {
					en.push(self.if_break_comma());
				}
				entry_items.push(self.arena.concat(&en));
			}
			self.push_between(
				&mut entry_items,
				before,
				After::End { at: span.end },
			);

			let concat = self.arena.concat(&entry_items);
			nodes.push(self.arena.indent(concat));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		self.arena.concat(&nodes)
	}

	/// `typeset Name: A + B { u32, u64 }`. Unlike an `enum`/`struct` body, the
	/// member list collapses onto one line when it fits `max_line_width` — but
	/// only when it holds no comments, since a `//` can never share a line with
	/// the member after it. With a comment present it breaks one-member-per-line
	/// and routes every gap through `push_between`, exactly like `enum`
	/// variants, so trailing comments and blank lines are preserved.
	fn build_typeset_definition(
		&mut self,
		span: TextSpan,
		pub_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		bounds: Option<ast::BoundId>,
		members: ast::List<ast::Path>,
	) -> NodeId {
		let ast = self.ast;
		let mut items: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			items.push(self.text(Text::Pub));
		}
		items.push(self.text(Text::Typeset));
		items.push(self.symbol(name.inner));
		if let Some(bounds) = bounds {
			items.push(self.text(Text::ColonSp));
			items.push(self.build_bound_expression(bounds));
		}
		let entries = ast
			.list(members)
			.iter()
			.map(|member| {
				let path = self.build_type_path(ast.list(member.segments));
				(member.span, path)
			})
			.collect();
		items.push(self.build_delimited_list(
			span,
			Text::SpaceLBrace,
			Text::RBrace,
			ListLayout::Padded,
			entries,
		));
		self.arena.concat(&items)
	}

	/// A struct's fields, or an enum's repr, each with its span.
	fn build_struct_fields(
		&mut self,
		fields: ast::List<ast::StructField>,
	) -> Vec<(TextSpan, NodeId)> {
		self.ast
			.spanned(fields)
			.map(|field| {
				let binding = self.build_binding_and_type(
					field.inner.binding,
					field.inner.ty,
				);
				let node = match field.inner.pub_at {
					Some(_) => {
						let keyword = self.text(Text::Pub);
						self.arena.concat(&[keyword, binding])
					}
					None => binding,
				};
				(field.span, node)
			})
			.collect()
	}

	fn build_struct_declaration(
		&mut self,
		span: TextSpan,
		name: &ast::Spanned<SymbolU32>,
		type_params: Option<NodeId>,
		fields: ast::List<ast::StructField>,
		pub_at: Option<TextOffset>,
	) -> NodeId {
		let mut items: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			items.push(self.text(Text::Pub));
		}
		items.push(self.text(Text::Struct));
		items.push(self.symbol(name.inner));
		items.extend(type_params);

		let entries = self.build_struct_fields(fields);
		items.push(self.build_delimited_list(
			span,
			Text::LParen,
			Text::RParen,
			ListLayout::Tight,
			entries,
		));
		items.push(self.text(Text::Semi));
		self.arena.concat(&items)
	}

	fn build_export_definition(
		&mut self,
		span: TextSpan,
		entries: ast::List<ast::ExportEntry>,
	) -> NodeId {
		let ast = self.ast;
		let mut items: Vec<NodeId> = vec![self.text(Text::ExportLBrace)];

		if entries.is_empty() {
			self.build_empty_braced_comments(&mut items, span);
		} else {
			let mut entry_items: Vec<NodeId> = Vec::new();
			let mut before = Before::Opener { from: span.start };
			for entry in ast.list(entries) {
				let entry_span = entry.span();
				self.push_between(
					&mut entry_items,
					before,
					After::Entry {
						start: entry_span.start,
					},
				);
				before = Before::Entry {
					end: entry_span.end,
				};

				let mut en: Vec<NodeId> = vec![self.build_export_entry(entry)];
				// An export block always breaks, so every entry ends with a
				// comma, the last one included.
				en.push(self.text(Text::Comma));
				entry_items.push(self.arena.concat(&en));
			}

			self.push_between(
				&mut entry_items,
				before,
				After::End { at: span.end },
			);

			let concat = self.arena.concat(&entry_items);
			items.push(self.arena.indent(concat));
			items.push(self.line());
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(&items)
	}

	/// `name` or `name as "external"`, without any separator.
	fn build_export_entry(&mut self, entry: &ast::ExportEntry) -> NodeId {
		let mut parts: Vec<NodeId> = vec![self.symbol(entry.name.inner)];
		if let Some(alias) = &entry.alias {
			parts.push(self.text(Text::As));
			parts.push(self.source_text(*alias));
		}
		self.arena.concat(&parts)
	}

	/// The body of a `{ }` that holds no entries. Only comments can be in
	/// there, and they are the list's like any others: an opener on one side,
	/// the closing brace on the other, which is exactly the fourth combination
	/// `push_between` already covers.
	/// A comma-separated list between `open` and `close`, as one group: on one
	/// line when it fits, otherwise one entry per line with a trailing comma.
	/// `entries` are each entry's span and its built node. A comment or a
	/// blank line the author left is kept, and keeps the list broken (see
	/// `push_between_breaking`). An empty list is `open`, its comments,
	/// `close`.
	fn build_delimited_list(
		&mut self,
		span: TextSpan,
		open: Text,
		close: Text,
		layout: ListLayout,
		entries: Vec<(TextSpan, NodeId)>,
	) -> NodeId {
		let open = self.text(open);
		let Some(&(last, _)) = entries.last() else {
			let mut items = vec![open];
			self.build_empty_braced_comments(&mut items, span);
			items.push(self.text(close));
			return self.arena.concat(&items);
		};
		let (end_break, entry_break) = match layout {
			ListLayout::Tight => (self.line(), self.soft_line()),
			ListLayout::Padded => (self.soft_line(), self.soft_line()),
			ListLayout::Broken => (self.hard_line(), self.hard_line()),
		};
		let count = entries.len();
		let mut inner: Vec<NodeId> = Vec::new();
		let mut previous_end = None;
		for (index, (entry_span, node)) in entries.into_iter().enumerate() {
			let (from, empty) = match previous_end {
				None => (Before::Opener { from: span.start }, end_break),
				Some(end) => (Before::Entry { end }, entry_break),
			};
			self.push_between_breaking(
				&mut inner,
				from,
				After::Entry {
					start: entry_span.start,
				},
				empty,
			);
			inner.push(node);
			inner.push(match index + 1 < count {
				true => self.text(Text::Comma),
				false => self.if_break_comma(),
			});
			previous_end = Some(entry_span.end);
		}
		// Comments before `close` end on a line of their own.
		let commented = self.push_between_breaking(
			&mut inner,
			Before::Entry { end: last.end },
			After::End { at: span.end },
			end_break,
		);
		let inner = self.arena.concat(&inner);
		let inner = self.arena.indent(inner);
		let end = match commented {
			true => self.hard_line(),
			false => end_break,
		};
		let close = self.text(close);
		let list = self.arena.concat(&[open, inner, end, close]);
		self.arena.group(list)
	}

	fn build_empty_braced_comments(
		&mut self,
		items: &mut Vec<NodeId>,
		span: TextSpan,
	) {
		let mut inner: Vec<NodeId> = Vec::new();
		self.push_between(
			&mut inner,
			Before::Opener { from: span.start },
			After::End { at: span.end },
		);
		if inner.is_empty() {
			return;
		}
		let inner_concat = self.arena.concat(&inner);
		items.push(self.arena.indent(inner_concat));
		items.push(self.hard_line());
	}

	/// An entry's attributes, each on its own line, with the comments around
	/// them, up to `start`, where the entry itself begins.
	fn build_attributes(
		&mut self,
		out: &mut Vec<NodeId>,
		attributes: ast::List<ast::Attribute>,
		start: TextOffset,
	) {
		let ast = self.ast;
		let spans = ast.spans(attributes);
		for (index, attr) in ast.spanned(attributes).enumerate() {
			out.push(self.text(Text::HashLBracket));
			out.push(self.symbol(attr.inner.name.inner));
			match attr.inner.value {
				ast::AttributeValue::Word => {}
				// Grouped as a call by name is, so it stays on the
				// attribute's line while it fits.
				ast::AttributeValue::Named(arguments) => {
					out.push(self.build_named_call_args(arguments, attr.span));
				}
			}
			out.push(self.text(Text::RBracket));
			let next = spans.get(index + 1).map_or(start, |span| span.start);
			self.push_between(
				out,
				Before::Attribute { end: attr.span.end },
				After::Entry { start: next },
			);
		}
	}

	/// Where an entry begins for the comments before it: at its first
	/// attribute, since the span of the entry itself starts after them.
	fn entry_start(
		&self,
		attributes: ast::List<ast::Attribute>,
		span: TextSpan,
	) -> TextOffset {
		self.ast
			.spans(attributes)
			.first()
			.map_or(span.start, |first| first.start)
	}

	/// `<...>` as written, or nothing when no list is written.
	fn build_type_params(
		&mut self,
		type_params: ast::List<ast::TypeParam>,
		span: Option<TextSpan>,
	) -> Option<NodeId> {
		if type_params.is_empty() {
			return None;
		}
		let span = span.expect("written type parameters have their span");
		let entries = self
			.ast
			.spanned(type_params)
			.map(|param| {
				let node = match param.inner {
					ast::TypeParam::Type { name, bounds } => {
						let name = self.symbol(name.inner);
						match bounds {
							Some(bounds) => {
								let colon = self.text(Text::ColonSp);
								let bounds =
									self.build_bound_expression(bounds);
								self.arena.concat(&[name, colon, bounds])
							}
							None => name,
						}
					}
					ast::TypeParam::Const { name, ty, .. } => {
						let keyword = self.text(Text::Const);
						let name = self.symbol(name.inner);
						let colon = self.text(Text::ColonSp);
						let ty = self.build_type_expression(ty);
						self.arena.concat(&[keyword, name, colon, ty])
					}
				};
				(param.span, node)
			})
			.collect();
		Some(self.build_delimited_list(
			span,
			Text::Lt,
			Text::Gt,
			ListLayout::Tight,
			entries,
		))
	}

	fn build_function_signature(
		&mut self,
		out: &mut Vec<NodeId>,
		signature: ast::SignatureId,
	) {
		let signature = self.ast.signature(signature);
		out.push(self.text(Text::Func));
		out.push(self.symbol(signature.name.inner));
		out.extend(self.build_type_params(
			signature.type_params,
			signature.type_params_span,
		));
		let entries = self
			.ast
			.spanned(signature.params)
			.map(|param| {
				let node = self.build_binding_and_type(
					param.inner.binding,
					param.inner.ty,
				);
				(param.span, node)
			})
			.collect();
		out.push(self.build_delimited_list(
			signature.params_span,
			Text::LParen,
			Text::RParen,
			ListLayout::Tight,
			entries,
		));
		if let Some(result) = &signature.result {
			out.push(self.text(Text::Arrow));
			out.push(self.build_type_expression(*result));
		}
	}

	/// A parameter or a field without its separator, as written.
	fn build_binding_and_type(
		&mut self,
		binding: ast::Binding,
		ty: Option<ast::TypeId>,
	) -> NodeId {
		let name = self.symbol(binding.name.inner);
		let binding = match binding.mut_at {
			Some(_) => {
				let keyword = self.text(Text::Mut);
				self.arena.concat(&[keyword, name])
			}
			None => name,
		};
		// A type left out is printed as written: the checker infers it or
		// reports it.
		match ty {
			Some(ty) => {
				let colon = self.text(Text::ColonSp);
				let ty = self.build_type_expression(ty);
				self.arena.concat(&[binding, colon, ty])
			}
			None => binding,
		}
	}

	fn build_global_definition(
		&mut self,
		pub_at: Option<TextOffset>,
		mut_at: Option<TextOffset>,
		name: &ast::Spanned<SymbolU32>,
		type_annotation: Option<ast::TypeId>,
		value: ast::ExprId,
	) -> NodeId {
		let mut items: Vec<NodeId> = Vec::new();
		if pub_at.is_some() {
			items.push(self.text(Text::Pub));
		}
		items.push(self.text(Text::Global));
		if mut_at.is_some() {
			items.push(self.text(Text::Mut));
		}
		items.push(self.symbol(name.inner));
		if let Some(annotation) = type_annotation {
			items.push(self.text(Text::ColonSp));
			items.push(self.build_type_expression(annotation));
		}
		items.push(self.text(Text::EqSp));
		items.push(self.build_expression(value));
		items.push(self.text(Text::Semi));
		self.arena.concat(&items)
	}

	fn build_fn_body(&mut self, block: ast::BlockId) -> NodeId {
		let span = self.ast.block_span(block);
		let entries = self.entries(block);
		if entries.is_empty() {
			return self.build_block_content(block, span);
		}

		// Function bodies always put their contents between hard brace lines.
		// Nested expressions retain their own independent layout groups.
		let mut inner = Vec::new();
		self.push_between(
			&mut inner,
			Before::Opener { from: span.start },
			After::Entry {
				start: self.entry_span(entries[0]).start,
			},
		);
		inner.push(self.build_block_statements(&entries, span));
		let inner = self.arena.concat(&inner);
		let open = self.text(Text::LBrace);
		let inner = self.arena.indent(inner);
		let line = self.hard_line();
		let close = self.text(Text::RBrace);
		self.arena.concat(&[open, inner, line, close])
	}

	/// A block's entries as written: its statements, then its tail.
	fn entries(&self, block: ast::BlockId) -> Vec<Entry> {
		let ast::Block { statements, tail } = self.ast.block(block);
		let statements = self.ast.list(statements).iter();
		statements
			.map(|&statement| Entry::Statement(statement))
			.chain(tail.map(Entry::Tail))
			.collect()
	}

	fn entry_span(&self, entry: Entry) -> TextSpan {
		match entry {
			Entry::Statement(statement) => self.ast.statement_span(statement),
			Entry::Tail(tail) => self.ast.expr_span(tail),
		}
	}

	/// Comments anywhere within a block prevent compact layout.
	fn block_has_comments(&self, block_span: TextSpan) -> bool {
		!self
			.comments
			.between(block_span.start, block_span.end)
			.is_empty()
	}

	/// Leaves brace lines ungrouped so paired `if` branches or a block-like
	/// expression can own the layout decision. `block_span` is where its
	/// comments are looked for: its braces, or from a keyword block's
	/// keyword.
	fn build_block_content(
		&mut self,
		block: ast::BlockId,
		block_span: TextSpan,
	) -> NodeId {
		let entries = self.entries(block);
		let mut items: Vec<NodeId> = vec![self.text(Text::LBrace)];

		if entries.is_empty() {
			self.build_empty_braced_comments(&mut items, block_span);
		} else {
			let single = matches!(
				*entries,
				[Entry::Tail(tail)] if !self.ast.expr(tail).is_block_like()
			) && !self.block_has_comments(block_span);
			let mut inner: Vec<NodeId> = Vec::new();
			if single {
				// No comments anywhere in here, so there is no gap to place —
				// only the break that may collapse and put the one statement
				// back on the brace's line.
				inner.push(self.soft_line());
			} else {
				self.push_between(
					&mut inner,
					Before::Opener {
						from: block_span.start,
					},
					After::Entry {
						start: self.entry_span(entries[0]).start,
					},
				);
			}

			inner.push(self.build_block_statements(&entries, block_span));

			let inner_concat = self.arena.concat(&inner);
			items.push(self.arena.indent(inner_concat));
			items.push(if single {
				self.soft_line()
			} else {
				self.hard_line()
			});
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(&items)
	}

	/// Statement separators and inter-entry comments are shared by function
	/// bodies and expression blocks; brace layout belongs to their callers.
	/// Every statement ends in `;`, a block-like one's only while it stays
	/// on one line, and the tail in none.
	fn build_block_statements(
		&mut self,
		entries: &[Entry],
		block_span: TextSpan,
	) -> NodeId {
		let mut inner = Vec::new();

		let mut previous_end = None;
		for (index, &entry) in entries.iter().enumerate() {
			let entry_span = self.entry_span(entry);
			// The break between two statements is emitted here rather
			// than at the end of the previous turn, so that turn can
			// close its line with `;` and let the gap append whatever
			// comment trails it.
			if let Some(end) = previous_end {
				self.push_between(
					&mut inner,
					Before::Entry { end },
					After::Entry {
						start: entry_span.start,
					},
				);
			}
			previous_end = Some(entry_span.end);
			let last = index + 1 == entries.len();
			match entry {
				Entry::Tail(tail) => inner.push(self.build_expression(tail)),
				Entry::Statement(statement) => {
					match self.ast.statement(statement) {
						ast::Statement::Expression(expression)
							if self.ast.expr(expression).is_block_like()
								&& !last =>
						{
							let semi = self.text(Text::Semi);
							let suffix = self.arena.alloc(Node::IfFlat(semi));
							// The suffix shares the expression's group so its
							// width and presence participate in the same layout
							// decision.
							let contents =
								self.build_expression_contents(expression);
							let contents =
								self.arena.concat(&[contents, suffix]);
							inner.push(self.arena.group(contents));
						}
						statement => {
							inner.push(self.build_statement(statement));
							inner.push(self.text(Text::Semi));
						}
					}
				}
			}
		}

		// Comments after the last statement. The first may still trail
		// its line; the rest stand on their own above the closing brace.
		self.push_between(
			&mut inner,
			Before::Entry {
				end: self.entry_span(*entries.last().unwrap()).end,
			},
			After::End { at: block_span.end },
		);

		self.arena.concat(&inner)
	}

	/// Keep a block-like value attached to its call or assignment opener,
	/// letting its own braces supply indentation rather than adding wrappers.
	fn is_huggable(&self, expr: ast::ExprId) -> bool {
		let expr = self.ungroup_expression(expr, ExpressionPosition::Whole);
		match self.ast.expr(expr) {
			kind if kind.is_block_like() => true,
			ast::Expression::Call { arguments, .. } => {
				match self.ast.argument_list(self.ungroup_list(arguments)) {
					ast::ArgumentList::Positional(&[argument]) => {
						self.is_huggable(argument)
					}
					ast::ArgumentList::Positional(_) => false,
					// A call by name is its own braces: they break open in
					// place.
					ast::ArgumentList::Named(_) => true,
				}
			}
			ast::Expression::NamedList { .. } => true,
			_ => false,
		}
	}

	/// The `.member` suffix and its turbofish, without rebuilding its object.
	fn build_member_suffix(&mut self, member: ast::PathSegment) -> NodeId {
		let dot = self.text(Text::Dot);
		let member = self.build_path_segment(member, Text::ColonColonLt);
		self.arena.concat(&[dot, member])
	}

	/// A call's argument list, by position or by name.
	fn build_arguments(&mut self, arguments: ast::ExprId) -> NodeId {
		match self.ast.expr(arguments) {
			ast::Expression::Tuple { .. } => {
				self.build_parenthesized_list(arguments)
			}
			ast::Expression::NamedList { arguments: named } => {
				self.build_named_call_args(named, self.ast.expr_span(arguments))
			}
			_ => unreachable!("an argument list is a tuple or a named list"),
		}
	}

	/// A named list's braces and entries, shared by calls and branch operands.
	fn build_named_call_args(
		&mut self,
		arguments: ast::List<ast::NamedArgument>,
		braces: TextSpan,
	) -> NodeId {
		let ast = self.ast;
		// A block value can't share a line, so it breaks the call.
		let has_block_value = ast.list(arguments).iter().any(|argument| {
			argument
				.value
				.is_some_and(|value| ast.expr(value).is_block_like())
		});
		let entries = ast
			.list(arguments)
			.iter()
			.map(|argument| {
				let mut nodes = vec![self.symbol(argument.name.inner)];
				let mut span = argument.name.span;
				if let Some(value) = argument.value {
					nodes.push(self.text(Text::ColonSp));
					nodes.push(self.build_expression(value));
					span.end = ast.expr_span(value).end;
				}
				(span, self.arena.concat(&nodes))
			})
			.collect();
		self.build_delimited_list(
			braces,
			Text::LBrace,
			Text::RBrace,
			match has_block_value {
				true => ListLayout::Broken,
				false => ListLayout::Padded,
			},
			entries,
		)
	}

	fn build_call_args(&mut self, arguments: &[ast::ExprId]) -> NodeId {
		let open = self.text(Text::LParen);
		let close = self.text(Text::RParen);
		let list = match arguments {
			[] => self.arena.concat(&[open, close]),
			&[argument] if self.is_huggable(argument) => {
				let argument = self.build_expression_at(
					argument,
					ExpressionPosition::ListElement,
				);
				self.arena.concat(&[open, argument, close])
			}
			_ => {
				let mut nodes = Vec::with_capacity(3 * arguments.len());
				nodes.push(self.line());
				for (index, &argument) in arguments.iter().enumerate() {
					nodes.push(self.build_expression_at(
						argument,
						ExpressionPosition::ListElement,
					));
					if index + 1 < arguments.len() {
						nodes.push(self.text(Text::Comma));
						nodes.push(self.soft_line());
					} else {
						nodes.push(self.if_break_comma());
					}
				}
				let arguments = self.arena.concat(&nodes);
				let arguments = self.arena.indent(arguments);
				let line = self.line();
				self.arena.concat(&[open, arguments, line, close])
			}
		};
		self.arena.group(list)
	}

	/// An `else { if .. }` wrapper is redundant only when the `if` is its
	/// sole value. Keep wrappers that terminate the value or own comments.
	fn else_if_expression(&self, block: ast::BlockId) -> Option<ast::ExprId> {
		let [Entry::Tail(expression)] = *self.entries(block) else {
			return None;
		};
		let span = self.ast.block_span(block);
		let expression_span = self.ast.expr_span(expression);
		if !matches!(self.ast.expr(expression), ast::Expression::IfElse { .. })
			|| !self
				.comments
				.between(span.start, expression_span.start)
				.is_empty()
			|| !self
				.comments
				.between(expression_span.end, span.end)
				.is_empty()
		{
			return None;
		}
		Some(expression)
	}

	/// Comments in the gaps around the elements belong to these delimiters.
	fn tuple_owns_comments(&self, expression: ast::ExprId) -> bool {
		let ast::Expression::Tuple { elements } = self.ast.expr(expression)
		else {
			unreachable!("expected a tuple");
		};
		let span = self.ast.expr_span(expression);
		let mut cursor = span.start;
		for &element in self.ast.list(elements) {
			let element = self.ast.expr_span(element);
			if !self.comments.between(cursor, element.start).is_empty() {
				return true;
			}
			cursor = element.end;
		}
		!self.comments.between(cursor, span.end).is_empty()
	}

	fn ungroup_expression(
		&self,
		mut expression: ast::ExprId,
		position: ExpressionPosition,
	) -> ast::ExprId {
		while let ast::Expression::Tuple { elements } =
			self.ast.expr(expression)
		{
			let &[inner] = self.ast.list(elements) else {
				break;
			};
			if self.tuple_owns_comments(expression) {
				break;
			}
			let kind = self.ast.expr(inner);
			let removable = match kind {
				ast::Expression::Tuple { .. } => true,
				ast::Expression::Ascription { .. } => {
					matches!(position, ExpressionPosition::ListElement)
				}
				// A named list is not an ordinary value. In particular,
				// `continue ({ i })` is not named state like `continue { i }`.
				ast::Expression::NamedList { .. } => false,
				kind if kind.is_block_like() => false,
				_ => match position {
					ExpressionPosition::Whole
					| ExpressionPosition::ListElement => true,
					ExpressionPosition::Callee => false,
					ExpressionPosition::Operand
					| ExpressionPosition::PostfixReceiver => {
						matches!(
							kind,
							ast::Expression::Path(_)
								| ast::Expression::QualifiedPath { .. }
								| ast::Expression::Grouped { .. }
								| ast::Expression::Placeholder
								| ast::Expression::String
								| ast::Expression::Char
								| ast::Expression::Call { .. }
								| ast::Expression::ObjectAccess { .. }
								| ast::Expression::Deref { .. }
								| ast::Expression::AddressOf { .. }
								| ast::Expression::Index { .. }
								| ast::Expression::ArrayList { .. }
								| ast::Expression::ArrayRepeat { .. }
						) || matches!(position, ExpressionPosition::Operand)
							&& matches!(
								kind,
								ast::Expression::Int { .. }
									| ast::Expression::Float
							)
					}
				},
			};
			if !removable {
				break;
			}
			expression = inner;
		}
		expression
	}

	/// The outer delimiters are required by the caller (a call, `if`, or
	/// `match`). Only a sole un-ascribed tuple can supply their contents;
	/// tuples occupying one of several positions must stay nested.
	fn ungroup_list(&self, expression: ast::ExprId) -> ast::ExprId {
		let ast = self.ast;
		let mut contents = expression;
		while let ast::Expression::Tuple { elements } = ast.expr(contents) {
			let &[inner] = ast.list(elements) else {
				break;
			};
			if !matches!(ast.expr(inner), ast::Expression::Tuple { .. })
				|| self.tuple_owns_comments(contents)
				|| self.tuple_owns_comments(inner)
			{
				break;
			}
			contents = inner;
		}
		contents
	}

	fn build_parenthesized_list(&mut self, expression: ast::ExprId) -> NodeId {
		let ast = self.ast;
		let span = ast.expr_span(expression);
		let contents = self.ungroup_list(expression);
		let ast::Expression::Tuple { elements } = ast.expr(contents) else {
			unreachable!("a parenthesized list is a tuple");
		};
		// Keep the compact, hugging layout for uncommented calls and tuples.
		if self.comments.between(span.start, span.end).is_empty() {
			return self.build_call_args(ast.list(elements));
		}
		let entries = ast
			.list(elements)
			.iter()
			.map(|&element| {
				(
					ast.expr_span(element),
					self.build_expression_at(
						element,
						ExpressionPosition::ListElement,
					),
				)
			})
			.collect();
		self.build_delimited_list(
			span,
			Text::LParen,
			Text::RParen,
			ListLayout::Tight,
			entries,
		)
	}

	fn build_expression(&mut self, expression: ast::ExprId) -> NodeId {
		self.build_expression_at(expression, ExpressionPosition::Whole)
	}

	fn build_expression_at(
		&mut self,
		expression: ast::ExprId,
		position: ExpressionPosition,
	) -> NodeId {
		let expression = self.ungroup_expression(expression, position);
		let contents = self.build_expression_contents(expression);
		if self.ast.expr(expression).is_block_like() {
			self.arena.group(contents)
		} else {
			contents
		}
	}

	/// A singleton subject is an expression, not a comma-separated layout:
	/// its operators provide the continuation breaks and indentation.
	fn build_subject(&mut self, expression: ast::ExprId) -> NodeId {
		let contents = self.ungroup_list(expression);
		let ast::Expression::Tuple { elements } = self.ast.expr(contents)
		else {
			unreachable!("a control-flow subject is a tuple");
		};
		if let &[value] = self.ast.list(elements)
			&& !self.tuple_owns_comments(expression)
			&& !self.tuple_owns_comments(contents)
		{
			let open = self.text(Text::LParen);
			let value = self
				.build_expression_at(value, ExpressionPosition::ListElement);
			let close = self.text(Text::RParen);
			let subject = self.arena.concat(&[open, value, close]);
			return self.arena.group(subject);
		}
		self.build_parenthesized_list(expression)
	}

	/// A value that cannot fit beside the prefix moves to the next line when
	/// it fits there whole. Otherwise it stays beside the prefix and breaks
	/// after its first operand; that operand moves down only when it cannot
	/// fit beside the prefix either.
	fn build_assignment_value(
		&mut self,
		prefix: NodeId,
		value: ast::ExprId,
		position: ExpressionPosition,
	) -> NodeId {
		if self.is_huggable(value) {
			let space = self.text(Text::Space);
			let value = self.build_expression_at(value, position);
			let assignment = self.arena.concat(&[prefix, space, value]);
			return self.arena.group(assignment);
		}
		let (first, continuation) =
			self.build_expression_parts(value, position);
		let gap = self.soft_line();
		let head = self.arena.concat(&[gap, first]);
		let head = self.arena.indent(head);
		let head = self.arena.group(head);
		let fallback = self.arena.append(head, continuation);
		let fallback = self.arena.group(fallback);
		let body = self.arena.append(first, continuation);
		let value = self.arena.alloc(Node::FlatBelow { body, fallback });
		self.arena.concat(&[prefix, value])
	}

	fn build_expression_parts(
		&mut self,
		expression: ast::ExprId,
		position: ExpressionPosition,
	) -> (NodeId, Option<NodeId>) {
		let expression = self.ungroup_expression(expression, position);
		match self.ast.expr(expression) {
			ast::Expression::Binary {
				left,
				operator,
				right,
				..
			} => self.build_binary_parts(left, operator, right),
			// The arguments, not the whole call, are the continuation.
			// Follow a receiver chain back to its first segment as well.
			ast::Expression::Call { callee, arguments } => {
				if matches!(
					self.ast.expr(callee),
					ast::Expression::ObjectAccess { .. }
				) && matches!(
					self.ast.expr(arguments),
					ast::Expression::Tuple { .. }
				) {
					return self.build_method_chain_parts(expression);
				}
				let (first, continuation) = self
					.build_expression_parts(callee, ExpressionPosition::Callee);
				let arguments = self.build_arguments(arguments);
				(first, Some(self.arena.prepend(continuation, arguments)))
			}
			ast::Expression::ObjectAccess { object, member } => {
				let (first, continuation) = self.build_expression_parts(
					object,
					ExpressionPosition::PostfixReceiver,
				);
				let suffix = self.build_member_suffix(self.ast.segment(member));
				(first, Some(self.arena.prepend(continuation, suffix)))
			}
			_ => (self.build_expression_at(expression, position), None),
		}
	}

	/// Successive calls have method-dot boundaries; an isolated method call
	/// or a field suffix alone does not introduce a chain layout.
	/// Every segment owns its argument group, so a broken chain need not
	/// break the arguments of a method that still fits on its own line.
	fn build_method_chain_parts(
		&mut self,
		expression: ast::ExprId,
	) -> (NodeId, Option<NodeId>) {
		let mut receiver = expression;
		let mut methods = Vec::new();
		while let ast::Expression::Call { callee, arguments } =
			self.ast.expr(receiver)
		{
			// A named call keeps its braces attached to its callee, as it
			// does outside a chain.
			if !matches!(
				self.ast.expr(arguments),
				ast::Expression::Tuple { .. }
			) {
				break;
			}
			let ast::Expression::ObjectAccess { object, member } =
				self.ast.expr(callee)
			else {
				break;
			};
			let member = self.build_member_suffix(self.ast.segment(member));
			let arguments = self.build_arguments(arguments);
			let method = self.arena.concat(&[member, arguments]);
			let method = self.arena.group(method);
			methods.push(method);
			receiver = object;
		}
		let base = self
			.ungroup_expression(receiver, ExpressionPosition::PostfixReceiver);
		let methods = match methods.as_slice() {
			[method]
				if !matches!(
					self.ast.expr(base),
					ast::Expression::Call { .. }
				) =>
			{
				*method
			}
			_ => {
				methods.reverse();
				for method in &mut methods {
					let line = self.line();
					let segment = self.arena.concat(&[line, *method]);
					*method = self.arena.indent(segment);
				}
				self.arena.concat(&methods)
			}
		};
		let (first, continuation) = self.build_expression_parts(
			receiver,
			ExpressionPosition::PostfixReceiver,
		);
		let continuation = continuation.map(|node| self.arena.group(node));
		(first, Some(self.arena.prepend(continuation, methods)))
	}

	fn build_binary_parts(
		&mut self,
		left: ast::ExprId,
		operator: ast::BinaryOp,
		right: ast::ExprId,
	) -> (NodeId, Option<NodeId>) {
		use ast::BinaryOp;
		if matches!(
			operator,
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
				| BinaryOp::RightShiftAssign
		) {
			let left =
				self.build_expression_at(left, ExpressionPosition::Operand);
			let space = self.text(Text::Space);
			let operator = self.text(Text::from(operator));
			let prefix = self.arena.concat(&[left, space, operator]);
			let assignment = self.build_assignment_value(
				prefix,
				right,
				ExpressionPosition::Operand,
			);
			return (assignment, None);
		}

		let mut operands = vec![right, left];
		let mut current = left;
		while let ast::Expression::Binary {
			left,
			operator: op,
			right,
			..
		} = self.ast.expr(current)
		{
			if op != operator {
				break;
			}
			*operands.last_mut().unwrap() = right;
			operands.push(left);
			current = left;
		}
		operands.reverse();
		let (first, first_continuation) = self
			.build_expression_parts(operands[0], ExpressionPosition::Operand);
		// The first operand can itself break (a call or a tighter binary
		// expression), independently of this chain's operator breaks.
		let first_continuation =
			first_continuation.map(|node| self.arena.group(node));
		let mut continuation = Vec::new();
		for &operand in &operands[1..] {
			let line = self.soft_line();
			let op = self.text(Text::from(operator));
			let space = self.text(Text::Space);
			let operand =
				self.build_expression_at(operand, ExpressionPosition::Operand);
			let part = self.arena.concat(&[line, op, space, operand]);
			continuation.push(self.arena.indent(part));
		}
		let continuation = self.arena.concat(&continuation);
		(
			first,
			Some(self.arena.prepend(first_continuation, continuation)),
		)
	}

	fn build_expression_contents(&mut self, expression: ast::ExprId) -> NodeId {
		let ast = self.ast;
		let span = ast.expr_span(expression);
		match ast.expr(expression) {
			ast::Expression::QualifiedPath { root, segments } => {
				let root = ast.qualified_root(root);
				let self_type_node = self.build_type_expression(root.self_type);
				let segments = self.build_value_path(ast.list(segments));
				self.build_qualified_path(
					self_type_node,
					Some(ast.list(root.trait_path)),
					segments,
				)
			}
			ast::Expression::Grouped { inner, segments } => {
				let inner_node = self.build_type_expression(inner);
				let segments = self.build_value_path(ast.list(segments));
				self.build_qualified_path(inner_node, None, segments)
			}
			ast::Expression::Path(path) => {
				self.build_value_path(ast.list(path))
			}
			ast::Expression::Binary {
				left,
				operator,
				right,
				..
			} => {
				let (first, continuation) =
					self.build_binary_parts(left, operator, right);
				let concat = self.arena.append(first, continuation);
				self.arena.group(concat)
			}
			ast::Expression::Block { label, block } => {
				// A plain block in expression position is spelled `block { .. }`;
				// the blocks owned by a construct (`if`, `loop`, a match arm, a
				// function body) go straight to `build_block_content`.
				let keyword = self.labelled_keyword(Text::Block, label);
				let content = self.build_block_content(block, span);
				self.arena.concat(&[keyword, content])
			}
			ast::Expression::Placeholder => self.text(Text::Underscore),
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let if_kw = self.text(Text::If);
				let cond = self.build_subject(condition);
				let sp = self.text(Text::Space);

				let else_data = else_block.map(|branch| match branch {
					ast::Branch::Block(block) => {
						if let Some(nested) = self.else_if_expression(block) {
							self.build_expression_contents(nested)
						} else {
							self.build_block_content(
								block,
								ast.block_span(block),
							)
						}
					}
					// A continuation belongs to the same layout group as the
					// first `if`, so every branch breaks when the chain breaks.
					ast::Branch::Expression(expr) => {
						self.build_expression_contents(expr)
					}
				});

				let then_id = self.build_block_content(
					then_block,
					ast.block_span(then_block),
				);
				let mut items: Vec<NodeId> = vec![if_kw, cond, sp, then_id];
				if let Some(else_id) = else_data {
					items.push(self.text(Text::Else));
					items.push(else_id);
				}
				self.arena.concat(&items)
			}
			ast::Expression::Loop {
				label,
				header,
				block,
			} => {
				let mut items = vec![self.labelled_keyword(Text::Loop, label)];
				// The parameters are laid out as a function's are, each
				// followed by its initial value.
				if let Some(header) = header {
					let ast::LoopHeader {
						params,
						initials,
						span,
					} = ast.loop_header(header);
					let entries = ast
						.spanned(params)
						.zip(ast.list(initials))
						.map(|(param, &initial)| {
							let end = ast.expr_span(initial).end;
							let span = TextSpan::new(param.span.start, end);
							let binding = self.build_binding_and_type(
								param.inner.binding,
								param.inner.ty,
							);
							let eq = self.text(Text::EqSp);
							let initial = self.build_expression(initial);
							(span, self.arena.concat(&[binding, eq, initial]))
						})
						.collect();
					items.push(self.build_delimited_list(
						span,
						Text::LParen,
						Text::RParen,
						ListLayout::Tight,
						entries,
					));
					items.push(self.text(Text::Space));
				}
				items.push(
					self.build_block_content(block, ast.block_span(block)),
				);
				self.arena.concat(&items)
			}
			ast::Expression::Match {
				scrutinee, arms, ..
			} => self.build_match_expression(span, scrutinee, ast.list(arms)),
			ast::Expression::Break { label, value } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Break)];
				if let Some(label) = label {
					items.push(self.text(Text::LabelColon));
					items.push(self.symbol(label.inner));
				}
				if let Some(value) = value {
					items.push(self.text(Text::Space));
					items.push(self.build_expression(value));
				}
				self.arena.concat(&items)
			}
			ast::Expression::Return { value } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Return)];
				if let Some(value) = value {
					items.push(self.text(Text::Space));
					items.push(self.build_expression(value));
				}
				self.arena.concat(&items)
			}
			ast::Expression::Continue { label, value } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Continue)];
				if let Some(label) = label {
					items.push(self.text(Text::LabelColon));
					items.push(self.symbol(label.inner));
				}
				if let Some(value) = value {
					items.push(self.text(Text::Space));
					items.push(self.build_expression(value));
				}
				let concat = self.arena.concat(&items);
				self.arena.group(concat)
			}
			ast::Expression::Int { .. } | ast::Expression::Float => {
				self.source_text(span)
			}
			// Any remaining singleton wrapper is required by its position,
			// its ascription, or its comments.
			ast::Expression::Tuple { elements }
				if let &[value] = ast.list(elements) =>
			{
				if self.tuple_owns_comments(expression) {
					return self.build_parenthesized_list(expression);
				}
				let open = self.text(Text::LParen);
				let val = self.build_expression_at(
					value,
					ExpressionPosition::ListElement,
				);
				let close = self.text(Text::RParen);
				self.arena.concat(&[open, val, close])
			}
			ast::Expression::Call { .. } => {
				let (first, continuation) = self.build_expression_parts(
					expression,
					ExpressionPosition::Whole,
				);
				let concat = self.arena.append(first, continuation);
				self.arena.group(concat)
			}
			ast::Expression::NamedList { arguments } => {
				self.build_named_call_args(arguments, span)
			}
			ast::Expression::Ascription { value, ty } => {
				let val = self.build_expression(value);
				let colon_sp = self.text(Text::ColonSp);
				let ty_id = self.build_type_expression(ty);
				self.arena.concat(&[val, colon_sp, ty_id])
			}
			ast::Expression::Error => unreachable!(),
			ast::Expression::Unary { operator, operand } => {
				let op_id = self.text(Text::from(operator));
				let operand_id = self
					.build_expression_at(operand, ExpressionPosition::Operand);
				self.arena.concat(&[op_id, operand_id])
			}
			ast::Expression::String | ast::Expression::Char => {
				self.source_text(span)
			}
			ast::Expression::ObjectAccess { object, member } => {
				let object = self.build_expression_at(
					object,
					ExpressionPosition::PostfixReceiver,
				);
				let suffix = self.build_member_suffix(ast.segment(member));
				self.arena.concat(&[object, suffix])
			}
			ast::Expression::Deref { pointer } => {
				let ptr_id = self.build_expression_at(
					pointer,
					ExpressionPosition::PostfixReceiver,
				);
				let dot_star = self.text(Text::DotStar);
				self.arena.concat(&[ptr_id, dot_star])
			}
			ast::Expression::AddressOf { value } => {
				let val_id = self.build_expression_at(
					value,
					ExpressionPosition::PostfixReceiver,
				);
				let suffix = self.text(Text::DotAmp);
				self.arena.concat(&[val_id, suffix])
			}
			ast::Expression::ArrayList { elements } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::LBracket)];
				for (i, &element) in ast.list(elements).iter().enumerate() {
					if i > 0 {
						items.push(self.text(Text::CommaSp));
					}
					items.push(self.build_expression(element));
				}
				items.push(self.text(Text::RBracket));
				self.arena.concat(&items)
			}
			ast::Expression::ArrayRepeat { value, count } => {
				let open = self.text(Text::LBracket);
				let val = self.build_expression(value);
				let semi_sp = self.text(Text::Semi);
				let sp = self.text(Text::Space);
				let cnt = self.build_const_argument(count);
				let close = self.text(Text::RBracket);
				self.arena.concat(&[open, val, semi_sp, sp, cnt, close])
			}
			ast::Expression::Index { object, index } => {
				let obj_id = self.build_expression_at(
					object,
					ExpressionPosition::PostfixReceiver,
				);
				let open = self.text(Text::LBracket);
				let idx = self.build_expression(index);
				let close = self.text(Text::RBracket);
				self.arena.concat(&[obj_id, open, idx, close])
			}
			ast::Expression::Tuple { .. } => {
				self.build_parenthesized_list(expression)
			}
		}
	}

	/// A pattern. What each term is follows from its own shape, so there is
	/// one way to print each of them: a name binds, a literal is printed as
	/// it was written, a qualified path compares with that constant, and a
	/// one-segment path is a constant marked with `const`.
	fn build_pattern(&mut self, out: &mut Vec<NodeId>, pattern: ast::PatId) {
		let ast = self.ast;
		match ast.pattern(pattern) {
			ast::Pattern::Wildcard => out.push(self.text(Text::Underscore)),
			ast::Pattern::Binding { mutable, name } => {
				if mutable {
					out.push(self.text(Text::Mut));
				}
				out.push(self.symbol(name.inner));
			}
			ast::Pattern::Constant { path } => {
				let path = ast.list(path);
				// A path of one segment can only be a constant the author
				// marked with `const`; a longer one is a constant already.
				if let [segment] = path
					&& segment.type_args.is_empty()
				{
					out.push(self.text(Text::Const));
				}
				out.push(self.build_value_path(path));
			}
			ast::Pattern::Literal(_) | ast::Pattern::Error => {
				out.push(self.source_text(ast.pattern_span(pattern)));
			}
			ast::Pattern::Or(alternatives) => {
				for (i, &alternative) in
					ast.list(alternatives).iter().enumerate()
				{
					if i > 0 {
						out.push(self.text(Text::VbarSp));
					}
					self.build_pattern(out, alternative);
				}
			}
			ast::Pattern::Destructure(destructure) => {
				self.build_destructure(out, destructure);
			}
		}
	}

	/// Destructuring; each of its children is a pattern of its own.
	fn build_destructure(
		&mut self,
		out: &mut Vec<NodeId>,
		destructure: ast::Destructure,
	) {
		let ast = self.ast;
		let elements =
			|this: &mut Self,
			 out: &mut Vec<NodeId>,
			 elements: &[ast::PatternElement]| {
				out.push(this.text(Text::LParen));
				for (i, element) in elements.iter().enumerate() {
					if i > 0 {
						out.push(this.text(Text::CommaSp));
					}
					match *element {
						ast::PatternElement::Pattern(pattern) => {
							this.build_pattern(out, pattern);
						}
						ast::PatternElement::Rest(_) => {
							out.push(this.text(Text::DotDot));
						}
					}
				}
				out.push(this.text(Text::RParen));
			};
		match destructure {
			// A tuple of one is its element, unless it groups alternatives.
			ast::Destructure::Tuple { elements: items }
				if let [ast::PatternElement::Pattern(pattern)] =
					*ast.list(items)
					&& !matches!(ast.pattern(pattern), ast::Pattern::Or(_)) =>
			{
				self.build_pattern(out, pattern);
			}
			ast::Destructure::Tuple { elements: items } => {
				elements(self, out, ast.list(items));
			}
			ast::Destructure::Struct {
				path,
				elements: items,
			} => {
				out.push(self.build_value_path(ast.list(path)));
				elements(self, out, ast.list(items));
			}
			ast::Destructure::NamedStruct { path, fields, .. } => {
				let fields = ast.list(fields);
				out.push(self.build_value_path(ast.list(path)));
				out.push(self.text(Text::LBrace));
				for (i, item) in fields.iter().enumerate() {
					out.push(self.text(if i > 0 {
						Text::CommaSp
					} else {
						Text::Space
					}));
					match *item {
						ast::PatternFieldItem::Field(field) => {
							out.push(self.symbol(field.name.inner));
							if let Some(pattern) = field.pattern {
								out.push(self.text(Text::ColonSp));
								self.build_pattern(out, pattern);
							}
						}
						ast::PatternFieldItem::Rest(_) => {
							out.push(self.text(Text::DotDot));
						}
					}
				}
				if !fields.is_empty() {
					out.push(self.text(Text::Space));
				}
				out.push(self.text(Text::RBrace));
			}
		}
	}

	fn build_statement(&mut self, statement: ast::Statement) -> NodeId {
		match statement {
			ast::Statement::Expression(expression) => {
				self.build_expression(expression)
			}
			ast::Statement::LocalDefinition {
				pattern,
				ty: type_annotation,
				value,
			} => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Local)];
				self.build_pattern(&mut items, pattern);
				if let Some(annotation) = type_annotation {
					items.push(self.text(Text::ColonSp));
					items.push(self.build_type_expression(annotation));
				}
				items.push(self.text(Text::EqBare));
				let prefix = self.arena.concat(&items);
				self.build_assignment_value(
					prefix,
					value,
					ExpressionPosition::Whole,
				)
			}
		}
	}

	/// A path in expression position: generic arguments use turbofish.
	fn build_value_path(&mut self, path: &[ast::PathSegment]) -> NodeId {
		self.build_path(path, Text::ColonColonLt)
	}

	fn build_path(&mut self, path: &[ast::PathSegment], open: Text) -> NodeId {
		let [first, rest @ ..] = path else {
			unreachable!("a path has a segment");
		};
		let first = self.build_path_segment(*first, open);
		if rest.is_empty() {
			return first;
		}
		let mut items = vec![first];
		for &segment in rest {
			items.push(self.text(Text::ColonColon));
			items.push(self.build_path_segment(segment, open));
		}
		self.arena.concat(&items)
	}

	/// A segment's name and its generic arguments, opened by `open`.
	fn build_path_segment(
		&mut self,
		segment: ast::PathSegment,
		open: Text,
	) -> NodeId {
		let name = self.symbol(segment.ident.inner);
		if segment.type_args.is_empty() {
			return name;
		}
		let mut items = vec![name, self.text(open)];
		for (i, &arg) in self.ast.list(segment.type_args).iter().enumerate() {
			if i > 0 {
				items.push(self.text(Text::CommaSp));
			}
			items.push(self.build_type_argument(arg));
		}
		items.push(self.text(Text::Gt));
		self.arena.concat(&items)
	}

	/// One `<...>` argument. A literal is printed as written, without the
	/// redundant `const` the parser dropped; a constant path keeps its own.
	fn build_type_argument(&mut self, arg: ast::TypeArgument) -> NodeId {
		match arg {
			ast::TypeArgument::Type(ty) => self.build_type_expression(ty),
			ast::TypeArgument::Const(constant) => {
				match self.ast.constant(constant) {
					ast::ConstArgument::Literal(_)
					| ast::ConstArgument::Infer => self.build_const_argument(constant),
					ast::ConstArgument::Error => unreachable!(),
					// Without its marker, a path is read as a type.
					ast::ConstArgument::Path(_)
					| ast::ConstArgument::QualifiedPath { .. }
					| ast::ConstArgument::Grouped { .. } => {
						let marker = self.text(Text::Const);
						let path = self.build_const_argument(constant);
						self.arena.concat(&[marker, path])
					}
				}
			}
		}
	}

	/// A constant as written, without a marker: where only a constant can
	/// be written (an array's length) one would be redundant.
	fn build_const_argument(&mut self, constant: ast::ConstId) -> NodeId {
		let ast = self.ast;
		match ast.constant(constant) {
			ast::ConstArgument::Literal(_) | ast::ConstArgument::Infer => {
				self.source_text(ast.const_span(constant))
			}
			ast::ConstArgument::Error => unreachable!(),
			ast::ConstArgument::Path(path) => {
				self.build_value_path(ast.list(path))
			}
			ast::ConstArgument::QualifiedPath { root, segments } => {
				let root = ast.qualified_root(root);
				let self_type = self.build_type_expression(root.self_type);
				let segments = self.build_value_path(ast.list(segments));
				self.build_qualified_path(
					self_type,
					Some(ast.list(root.trait_path)),
					segments,
				)
			}
			ast::ConstArgument::Grouped { inner, segments } => {
				let inner = self.build_type_expression(inner);
				let segments = self.build_value_path(ast.list(segments));
				self.build_qualified_path(inner, None, segments)
			}
		}
	}

	/// A path in type position: generic arguments are bare, `Point<i32>`,
	/// never turbofish.
	fn build_type_path(&mut self, path: &[ast::PathSegment]) -> NodeId {
		self.build_path(path, Text::Lt)
	}

	/// Formats `<self_type_node [as trait_segments]>::segments` — shared by
	/// `QualifiedPath` (`<Type as Trait>::Item`, `trait_segments: Some`) and
	/// `Grouped` (`<Type>::Item`, `trait_segments: None`) in both type
	/// position and expression position, which differ only in how
	/// `self_type_node` and `segments` were built: the trait is always a type
	/// path, the trailing segments follow the position (bare `<..>` in a type,
	/// turbofish in an expression).
	fn build_qualified_path(
		&mut self,
		self_type_node: NodeId,
		trait_segments: Option<&[ast::PathSegment]>,
		segments: NodeId,
	) -> NodeId {
		let mut items: Vec<NodeId> = vec![self.text(Text::Lt), self_type_node];
		if let Some(trait_segments) = trait_segments {
			items.push(self.text(Text::As));
			items.push(self.build_type_path(trait_segments));
		}
		items.push(self.text(Text::Gt));
		items.push(self.text(Text::ColonColon));
		items.push(segments);
		self.arena.concat(&items)
	}

	fn build_bound_expression(&mut self, bound: ast::BoundId) -> NodeId {
		let ast = self.ast;
		match ast.bound(bound) {
			ast::BoundExpression::Error => unreachable!(),
			ast::BoundExpression::Path(segs) => {
				self.build_type_path(ast.list(segs))
			}
			ast::BoundExpression::WithBindings {
				path,
				bindings,
				open_brace,
			} => {
				// `where { A = u32, B: Tr }` when it fits; otherwise one
				// binding per line, as other braced lists break.
				let base_id = self.build_type_path(ast.list(path));
				let where_kw = self.text(Text::Where);
				let entries = ast
					.list(bindings)
					.iter()
					.map(|binding| {
						let mut key = self.symbol(binding.name.inner);
						if let ast::AssocBindingKind::ConstRepresentable {
							..
						}
						| ast::AssocBindingKind::ConstEquals { .. } =
							binding.kind
						{
							let marker = self.text(Text::Const);
							key = self.arena.concat(&[marker, key]);
						}
						let rhs = match binding.kind {
							ast::AssocBindingKind::Equals(ty) => {
								let eq = self.text(Text::EqSp);
								let ty = self.build_type_expression(ty);
								self.arena.concat(&[eq, ty])
							}
							ast::AssocBindingKind::Bound(bound) => {
								let colon = self.text(Text::ColonSp);
								let bound = self.build_bound_expression(bound);
								self.arena.concat(&[colon, bound])
							}
							ast::AssocBindingKind::ConstRepresentable {
								ty,
								..
							} => {
								let colon = self.text(Text::ColonSp);
								let ty = self.build_type_expression(ty);
								self.arena.concat(&[colon, ty])
							}
							ast::AssocBindingKind::ConstEquals {
								value,
								..
							} => {
								let eq = self.text(Text::EqSp);
								let value = self.build_const_argument(value);
								self.arena.concat(&[eq, value])
							}
						};
						(binding.span, self.arena.concat(&[key, rhs]))
					})
					.collect();
				let braces =
					TextSpan::new(open_brace, ast.bound_span(bound).end);
				let block = self.build_delimited_list(
					braces,
					Text::LBrace,
					Text::RBrace,
					ListLayout::Padded,
					entries,
				);
				self.arena.concat(&[base_id, where_kw, block])
			}
			// `A + B + C` when it fits; otherwise one bound per line, each led
			// by its `+`, indented under the line that names the list:
			//
			//     pub typeset PointerSize:
			//         + Add
			//         + Sub {
			ast::BoundExpression::BoundList(items) => {
				let line = self.line();
				let lead = self.text(Text::PlusLead);
				let lead = self.arena.alloc(Node::IfBroken(lead));
				let mut parts: Vec<NodeId> = vec![line, lead];
				for (i, &b) in ast.list(items).iter().enumerate() {
					if i > 0 {
						parts.push(self.soft_line());
						parts.push(self.text(Text::PlusLead));
					}
					parts.push(self.build_bound_expression(b));
				}
				let parts = self.arena.concat(&parts);
				let indented = self.arena.indent(parts);
				self.arena.group(indented)
			}
		}
	}

	/// The `heap::` written ahead of a pointer, slice or array sigil to name
	/// its memory explicitly; nothing when it was left to ambient resolution.
	fn build_memory_tag(
		&mut self,
		out: &mut Vec<NodeId>,
		memory: Option<&[ast::PathSegment]>,
	) {
		if let Some(memory) = memory {
			out.push(self.build_type_path(memory));
			out.push(self.text(Text::ColonColon));
		}
	}

	fn build_type_expression(&mut self, ty: ast::TypeId) -> NodeId {
		let ast = self.ast;
		match ast.ty(ty) {
			ast::TypeExpression::QualifiedPath { root, segments } => {
				let root = ast.qualified_root(root);
				let self_type_node = self.build_type_expression(root.self_type);
				let segments = self.build_type_path(ast.list(segments));
				self.build_qualified_path(
					self_type_node,
					Some(ast.list(root.trait_path)),
					segments,
				)
			}
			ast::TypeExpression::Grouped { inner, segments } => {
				let inner_node = self.build_type_expression(inner);
				let segments = self.build_type_path(ast.list(segments));
				self.build_qualified_path(inner_node, None, segments)
			}
			// The formatter never runs on a file that failed to parse.
			ast::TypeExpression::Error => unreachable!(),
			ast::TypeExpression::Infer => self.text(Text::Underscore),
			ast::TypeExpression::Never => self.text(Text::Bang),
			ast::TypeExpression::Path(path) => {
				self.build_type_path(ast.list(path))
			}
			ast::TypeExpression::Function {
				params,
				params_span,
				result,
			} => {
				let entries = ast
					.list(params)
					.iter()
					.map(|param| {
						let ty = self.build_type_expression(param.ty);
						let node = match param.name {
							Some(name) => {
								let name = self.symbol(name.inner);
								let colon = self.text(Text::ColonSp);
								self.arena.concat(&[name, colon, ty])
							}
							None => ty,
						};
						(param.span, node)
					})
					.collect();
				let params = self.build_delimited_list(
					params_span,
					Text::FuncParen,
					Text::RParen,
					ListLayout::Tight,
					entries,
				);
				match result {
					Some(result) => {
						let arrow = self.text(Text::Arrow);
						let result = self.build_type_expression(result);
						self.arena.concat(&[params, arrow, result])
					}
					None => params,
				}
			}
			ast::TypeExpression::Pointer {
				ownership,
				memory,
				inner,
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				self.build_memory_tag(
					&mut items,
					memory.map(|memory| ast.list(memory)),
				);
				items.push(self.text(ownership_sigil(ownership)));
				items.push(self.build_type_expression(inner));
				self.arena.concat(&items)
			}
			ast::TypeExpression::Slice { inner } => {
				let items = vec![
					self.text(Text::LBracket),
					self.build_type_expression(inner),
					self.text(Text::RBracket),
				];
				self.arena.concat(&items)
			}
			ast::TypeExpression::Array { inner, length } => {
				let items = vec![
					self.text(Text::LBracket),
					self.build_type_expression(inner),
					self.text(Text::Semi),
					self.text(Text::Space),
					self.build_const_argument(length),
					self.text(Text::RBracket),
				];
				self.arena.concat(&items)
			}
			// A tuple of one is its element.
			ast::TypeExpression::Tuple { elements } if elements.len() == 1 => {
				self.build_type_expression(ast.list(elements)[0])
			}
			ast::TypeExpression::Tuple { elements } => {
				let entries = ast
					.list(elements)
					.iter()
					.map(|&element| {
						let span = ast.type_span(element);
						(span, self.build_type_expression(element))
					})
					.collect();
				self.build_delimited_list(
					ast.type_span(ty),
					Text::LParen,
					Text::RParen,
					ListLayout::Tight,
					entries,
				)
			}
		}
	}
}

#[derive(Clone, Copy)]
pub struct RendererConfig {
	pub max_line_width: u32,
	pub indent_width: u8,
	pub line_ending: LineEnding,
}

impl Default for RendererConfig {
	fn default() -> Self {
		Self {
			max_line_width: 80,
			indent_width: 4,
			line_ending: LineEnding::Lf,
		}
	}
}

/// The line break the formatter prints.
#[derive(serde::Deserialize, Default, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum LineEnding {
	#[default]
	Lf,
	Crlf,
}

/// The formatter's view of a `wx.json`: only its `format` section, every
/// other key ignored. Each field is optional, so a manifest can override
/// one setting without restating the others.
#[derive(serde::Deserialize)]
struct Manifest {
	#[serde(default)]
	format: FormatSection,
}

#[derive(serde::Deserialize, Default)]
struct FormatSection {
	max_line_width: Option<u32>,
	indent_width: Option<u8>,
	line_ending: Option<LineEnding>,
}

impl RendererConfig {
	/// Reads the `format` section of the `wx.json` text `manifest` and
	/// overlays it onto the defaults, field by field.
	///
	/// Lives here rather than in either caller because `wx format` and the
	/// LSP's formatting request must agree byte for byte — formatting a
	/// file on save and formatting it from the CLI are the same operation,
	/// and two copies of this overlay would be free to drift apart.
	pub fn from_manifest(manifest: &str) -> Result<Self, serde_json::Error> {
		let Manifest { format } = serde_json::from_str(manifest)?;
		let default = Self::default();
		Ok(Self {
			max_line_width: format
				.max_line_width
				.unwrap_or(default.max_line_width),
			indent_width: format.indent_width.unwrap_or(default.indent_width),
			line_ending: format.line_ending.unwrap_or(default.line_ending),
		})
	}
}

struct Renderer<'a> {
	config: RendererConfig,
	interner: &'a ast::StringInterner,
	source: &'a str,
	arena: &'a Arena,
	buffer: String,
	position: usize,
	indent: usize,
	/// `fits`'s work list, a field so each group's decision reuses it.
	unmeasured: Vec<Unmeasured>,
}

#[derive(Clone, Copy)]
enum RenderMode {
	Flat,
	Break,
}

impl<'a> Renderer<'a> {
	fn new(
		config: RendererConfig,
		interner: &'a ast::StringInterner,
		source: &'a str,
		arena: &'a Arena,
	) -> Self {
		Self {
			config,
			interner,
			source,
			arena,
			buffer: String::new(),
			position: 0,
			indent: 0,
			unmeasured: Vec::new(),
		}
	}

	/// Renders the document from an explicit stack of what is left to print,
	/// as Wadler's and Prettier's printers do, so a group's decision can see
	/// what follows it (`fits`).
	fn render(mut self, root: NodeId) -> String {
		let mut rest = vec![Command {
			id: root,
			indent: 0,
			mode: RenderMode::Break,
		}];
		while let Some(command) = rest.pop() {
			self.indent = command.indent;
			self.render_node(command, &mut rest);
		}
		self.buffer
	}

	/// Ends the current line, dropping indentation that turned out to have
	/// nothing after it. Every line break goes through here or
	/// `newline_indented`, so no line can end in whitespace — a blank line
	/// between two indented statements is a bare `\n` rather than `\n` plus
	/// the indent the following line re-emits anyway.
	///
	/// A break with nothing in front of it *opens* the first line rather than
	/// ending an empty one, so the output never starts blank. That is what
	/// lets a list's head gap be emitted unconditionally: at the top of a file
	/// there is no opener line to close, and the break simply disappears.
	fn newline(&mut self) {
		self.buffer
			.truncate(self.buffer.trim_end_matches(' ').len());
		if self.buffer.is_empty() {
			return;
		}
		match self.config.line_ending {
			LineEnding::Lf => self.buffer.push('\n'),
			LineEnding::Crlf => self.buffer.push_str("\r\n"),
		}
	}

	/// Ends the current line and opens the next one at the current indent.
	fn newline_indented(&mut self) {
		self.newline();
		self.buffer.extend(std::iter::repeat_n(' ', self.indent));
		self.position = self.indent;
	}

	/// Prints `command`'s node, or pushes its parts onto `rest`, the stack of
	/// what is left to print (its top is printed next).
	fn render_node(&mut self, command: Command, rest: &mut Vec<Command>) {
		let Command { id, indent, mode } = command;
		let part = |id| Command { id, indent, mode };
		match self.arena.nodes[id.index()] {
			Node::Text(t) => {
				let s = t.as_str();
				self.buffer.push_str(s);
				self.position += s.len();
			}
			Node::SourceText(span) => {
				let text = span.extract_str(self.source);
				self.buffer.push_str(text);
				self.position = text
					.rsplit_once('\n')
					.map_or(self.position + text.len(), |(_, last)| last.len());
			}
			Node::Symbol { symbol, .. } => {
				let resolved = self.interner.resolve(symbol).unwrap();
				self.buffer.push_str(resolved);
				self.position += resolved.len();
			}
			Node::SoftLine => match mode {
				RenderMode::Flat => {
					self.buffer.push(' ');
					self.position += 1;
				}
				RenderMode::Break => self.newline_indented(),
			},
			Node::Line => match mode {
				RenderMode::Flat => {}
				RenderMode::Break => self.newline_indented(),
			},
			Node::BlankLine => {
				self.newline();
				self.position = 0;
			}
			Node::HardLine => self.newline_indented(),
			Node::Concat { start, len } => {
				for i in (start as usize..(start + len) as usize).rev() {
					rest.push(part(self.arena.children[i]));
				}
			}
			Node::Group(inner) => {
				let mode = match mode {
					RenderMode::Flat => RenderMode::Flat,
					RenderMode::Break => {
						let width = (self.config.max_line_width as usize)
							.saturating_sub(self.position);
						match self.fits(inner, rest, width) {
							true => RenderMode::Flat,
							false => RenderMode::Break,
						}
					}
				};
				rest.push(Command {
					id: inner,
					indent,
					mode,
				});
			}
			Node::Indent(inner) => rest.push(Command {
				id: inner,
				indent: indent + self.config.indent_width as usize,
				mode,
			}),
			Node::IfFlat(fragment) if matches!(mode, RenderMode::Flat) => {
				rest.push(part(fragment));
			}
			Node::IfBroken(fragment) if matches!(mode, RenderMode::Break) => {
				rest.push(part(fragment));
			}
			Node::IfFlat(_) | Node::IfBroken(_) => {}
			Node::FlatBelow { body, fallback } => {
				let max = self.config.max_line_width as usize;
				let below = indent + self.config.indent_width as usize;
				let flat = |id, indent| Command {
					id,
					indent,
					mode: RenderMode::Flat,
				};
				if matches!(mode, RenderMode::Flat)
					|| self.fits(
						fallback,
						rest,
						max.saturating_sub(self.position),
					) {
					rest.push(flat(fallback, indent));
				} else if self.fits(body, rest, max.saturating_sub(below)) {
					self.indent = below;
					self.newline_indented();
					rest.push(flat(body, below));
				} else {
					rest.push(part(fallback));
				}
			}
		}
	}

	/// Whether `group`, laid out flat, fits in `width` together with what
	/// follows it on the same line: the commands in `rest`, in their own
	/// modes, up to the first line break one of them takes. A group still
	/// to be decided there counts as broken, so its first possible break ends
	/// the line (it can always take it). A hard break, or source text over
	/// several lines, inside `group` means it cannot be flat at all.
	fn fits(&mut self, group: NodeId, rest: &[Command], width: usize) -> bool {
		self.unmeasured.clear();
		self.unmeasured.push(Unmeasured {
			id: group,
			mode: RenderMode::Flat,
			follows: false,
		});
		let mut width = width as isize;
		let mut next_rest = rest.len();
		loop {
			let entry = match self.unmeasured.pop() {
				Some(entry) => entry,
				None => {
					let Some(index) = next_rest.checked_sub(1) else {
						return true;
					};
					next_rest = index;
					Unmeasured {
						id: rest[index].id,
						mode: rest[index].mode,
						follows: true,
					}
				}
			};
			let Unmeasured { id, mode, follows } = entry;
			match self.arena.nodes[id.index()] {
				Node::Text(t) => width -= t.as_str().len() as isize,
				Node::SourceText(span) => {
					let text = span.extract_str(self.source);
					match text.find(['\n', '\r']) {
						None => width -= text.len() as isize,
						Some(_) if !follows => return false,
						Some(line_end) => {
							return width >= line_end as isize;
						}
					}
				}
				Node::Symbol { len, .. } => width -= len as isize,
				Node::SoftLine | Node::Line => match mode {
					RenderMode::Flat => {
						if let Node::SoftLine = self.arena.nodes[id.index()] {
							width -= 1;
						}
					}
					RenderMode::Break => return true,
				},
				Node::BlankLine | Node::HardLine => return follows,
				Node::Concat { start, len } => {
					for i in (start as usize..(start + len) as usize).rev() {
						self.unmeasured.push(Unmeasured {
							id: self.arena.children[i],
							..entry
						});
					}
				}
				Node::Group(inner) | Node::Indent(inner) => {
					self.unmeasured.push(Unmeasured { id: inner, ..entry });
				}
				Node::IfFlat(fragment) => {
					if let RenderMode::Flat = mode {
						self.unmeasured.push(Unmeasured {
							id: fragment,
							..entry
						});
					}
				}
				Node::IfBroken(fragment) => {
					if let RenderMode::Break = mode {
						self.unmeasured.push(Unmeasured {
							id: fragment,
							..entry
						});
					}
				}
				// Undecided, it may open the next line right away.
				Node::FlatBelow { fallback, .. } => match mode {
					RenderMode::Flat => self.unmeasured.push(Unmeasured {
						id: fallback,
						..entry
					}),
					RenderMode::Break => return true,
				},
			}
			if width < 0 {
				return false;
			}
		}
	}
}

/// A node `fits` has yet to measure, and the mode it is measured in.
#[derive(Clone, Copy)]
struct Unmeasured {
	id: NodeId,
	mode: RenderMode,
	/// Whether the node comes after the group being decided (from `rest`)
	/// rather than inside it: a line break there ends the line, one inside
	/// the group means the group cannot be flat.
	follows: bool,
}

/// One thing left to print: a node, the indentation its lines open at, and
/// the mode of the group it is in.
#[derive(Clone, Copy)]
struct Command {
	id: NodeId,
	indent: usize,
	mode: RenderMode,
}

fn ownership_sigil(ownership: ast::Ownership) -> Text {
	match ownership {
		ast::Ownership::Exclusive => Text::Star,
		ast::Ownership::Shared => Text::Amp,
	}
}

pub fn format(
	ast: &ast::AST,
	comments: &ast::CommentMap,
	interner: &ast::StringInterner,
	source: &str,
	config: RendererConfig,
) -> String {
	let mut builder = Builder {
		interner,
		source,
		ast,
		comments,
		arena: Arena::new(),
	};
	let body = builder.build(ast);
	let hl = builder.hard_line();
	let root = builder.arena.prepend(body, hl);
	let Builder { arena, .. } = builder;
	Renderer::new(config, interner, source, &arena).render(root)
}
