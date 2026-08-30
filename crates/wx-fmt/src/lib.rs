use string_interner::symbol::SymbolU32;
use wx_compiler::ast;

#[cfg(test)]
mod tests;

type NodeId = u32;

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
		Fn      => "fn ",
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
		// keywords without trailing space
		Break       => "break",
		Continue    => "continue",
		Return      => "return",
		Unreachable => "unreachable",
		True        => "true",
		False       => "false",
		// punctuation
		Semi             => ";",
		Comma            => ",",
		Dot              => ".",
		DotStar          => ".*",
		DotAmp           => ".&",
		DotDot           => "..",
		LBrace           => "{",
		LBraceSpace      => "{ ",
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
		ColonColon       => "::",
		ColonColonLt     => "::<",
		ColonColonLBrace => "::{",
		// spaced punctuation / keywords
		Arrow            => " -> ",
		As               => " as ",
		ColonSp          => ": ",
		CommaSp          => ", ",
		PlusSp           => " + ",
		EqSp             => " = ",
		EqBare           => " =",
		Else             => " else ",
		ForKw            => " for ",
		LabelColon       => " :",
		Space            => " ",
		SpaceLBrace      => " {",
		SpaceLBraceSpace => " { ",
		SpaceRBrace      => " }",
		Where        => " where ",
		// compound tokens
		ExportLBrace => "export {",
		FnParen      => "fn(",
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
		// unary-only
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
	SourceText(ast::TextSpan),
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
	/// A sequence of nodes concatenated together
	/// Children stored in `Arena::children[start .. start + len]`.
	Concat {
		start: u32,
		len: u32,
	},
	/// All lines under this node must either break or not break together
	Group(NodeId),
	/// Increases the indentation level for all lines within this node
	Indent(NodeId),
	/// A trailing comma emitted only in Break mode
	IfBreakComma,
}

/// TODO: about half of what this holds is duplicates. `Node::HardLine`,
/// `SoftLine`, `Line`, `BlankLine`, `IfBreakComma` and `Node::Text(_)` carry
/// nothing to tell two of them apart, yet every `hard_line()`/`text()` call
/// allocates a fresh one — measured over `std/main.wx`, 19% of nodes are line
/// breaks and 32% are fixed tokens, drawn from ~95 distinct values in total.
///
/// The fix is to allocate each of those once in `new()` and hand out the id:
/// a `Box<[NodeId]>` indexed by `token as usize` (the `define_text!` macro
/// would emit the variant list), plus one field per line-break kind. It is
/// safe — nothing mutates a node after it is built, and the renderer decides
/// everything from the current mode and indent, never from node identity.
/// Left undone deliberately; the formatter is not on any hot path today.
struct Arena {
	nodes: Vec<Node>,
	children: Vec<NodeId>,
}

impl Arena {
	fn new() -> Self {
		Self {
			nodes: Vec::new(),
			children: Vec::new(),
		}
	}

	#[inline]
	fn alloc(&mut self, node: Node) -> NodeId {
		let id = self.nodes.len() as u32;
		self.nodes.push(node);
		id
	}

	fn concat(&mut self, children: Vec<NodeId>) -> NodeId {
		match children.len() {
			0 => self.alloc(Node::Concat { start: 0, len: 0 }),
			1 => children[0],
			_ => {
				let start = self.children.len() as u32;
				let len = children.len() as u32;
				self.children.extend_from_slice(&children);
				self.alloc(Node::Concat { start, len })
			}
		}
	}

	#[inline]
	fn concat2(&mut self, a: NodeId, b: NodeId) -> NodeId {
		let start = self.children.len() as u32;
		self.children.push(a);
		self.children.push(b);
		self.alloc(Node::Concat { start, len: 2 })
	}

	#[inline]
	fn concat3(&mut self, a: NodeId, b: NodeId, c: NodeId) -> NodeId {
		let start = self.children.len() as u32;
		self.children.push(a);
		self.children.push(b);
		self.children.push(c);
		self.alloc(Node::Concat { start, len: 3 })
	}

	#[inline]
	fn concat4(
		&mut self,
		a: NodeId,
		b: NodeId,
		c: NodeId,
		d: NodeId,
	) -> NodeId {
		let start = self.children.len() as u32;
		self.children.push(a);
		self.children.push(b);
		self.children.push(c);
		self.children.push(d);
		self.alloc(Node::Concat { start, len: 4 })
	}

	#[inline]
	fn concat5(
		&mut self,
		a: NodeId,
		b: NodeId,
		c: NodeId,
		d: NodeId,
		e: NodeId,
	) -> NodeId {
		let start = self.children.len() as u32;
		self.children.push(a);
		self.children.push(b);
		self.children.push(c);
		self.children.push(d);
		self.children.push(e);
		self.alloc(Node::Concat { start, len: 5 })
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

struct Builder<'a> {
	interner: &'a ast::StringInterner,
	source: &'a str,
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
	Opener { from: u32 },
	/// The end of an entry's content. A comment on that same line trails it,
	/// and a blank line the author left is kept.
	Entry { end: u32 },
	/// An entry that always stands apart from the next — a block-like item, an
	/// impl member. Like `Entry`, but a blank line goes in even where the
	/// author left none. Paired with `After::End` it degenerates to `Entry`:
	/// there is nothing following for it to stand apart from.
	SpacedEntry { end: u32 },
}

/// What sits *after* a gap. Decides only whether a line is opened once the
/// comments have been placed.
#[derive(Clone, Copy)]
enum After {
	/// Another entry begins at `start`. Its line is opened once the comments
	/// are placed, so an empty gap is just the line break and the caller can
	/// push the entry straight on.
	Entry { start: u32 },
	/// The list ends at `at` — a closing brace, or the end of the file. That
	/// bounds which comments belong to the gap and nothing more: no line is
	/// opened, because nothing follows.
	End { at: u32 },
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

impl<'a> Builder<'a> {
	#[inline]
	fn text(&mut self, t: Text) -> NodeId {
		self.arena.alloc(Node::Text(t))
	}

	#[inline]
	fn hard_line(&mut self) -> NodeId {
		self.arena.alloc(Node::HardLine)
	}

	#[inline]
	fn soft_line(&mut self) -> NodeId {
		self.arena.alloc(Node::SoftLine)
	}

	#[inline]
	fn line(&mut self) -> NodeId {
		self.arena.alloc(Node::Line)
	}

	#[inline]
	fn blank_line(&mut self) -> NodeId {
		self.arena.alloc(Node::BlankLine)
	}

	#[inline]
	fn if_break_comma(&mut self) -> NodeId {
		self.arena.alloc(Node::IfBreakComma)
	}

	#[inline]
	fn symbol(&mut self, symbol: SymbolU32) -> NodeId {
		let len = self.interner.resolve(symbol).unwrap().len() as u32;
		self.arena.alloc(Node::Symbol { symbol, len })
	}

	#[inline]
	fn source_text(&mut self, span: ast::TextSpan) -> NodeId {
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
		prev_end: u32,
		gap: &'a [ast::Comment],
	) -> (Option<&'a ast::Comment>, &'a [ast::Comment]) {
		match gap.split_first() {
			Some((first, rest))
				if first.kind != ast::CommentKind::Doc
					&& !self.source
						[prev_end as usize..first.span.start as usize]
						.contains('\n')
					&& !self.source[..prev_end as usize]
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
		from: u32,
		to: u32,
		blank: Blank,
	) {
		let wants_blank = match blank {
			Blank::Force => true,
			Blank::Suppress => false,
			Blank::Preserve => {
				Self::has_blank_line(self.source, from as usize, to as usize)
			}
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
		cursor: u32,
		comments: &[ast::Comment],
		first: Blank,
	) -> u32 {
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
		let (start, first_blank, may_trail) = match from {
			Before::Opener { from } => (from, Blank::Suppress, false),
			Before::Entry { end } => (end, Blank::Preserve, true),
			Before::SpacedEntry { end } => (end, Blank::Force, true),
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
			self.push_line_break(out, cursor, next, blank);
		}
	}

	fn build(&mut self, ast: &ast::AST) -> NodeId {
		self.build_item_list(
			&ast.items,
			ast::TextSpan::new(0, self.source.len() as u32),
		)
	}

	/// `span` bounds the region the items live in — the whole file, or a `mod`
	/// body. Comments before the first item and after the last one belong to
	/// the list too, so both ends of `span` matter.
	fn build_item_list(
		&mut self,
		items: &[ast::Separated<ast::Spanned<ast::Item>>],
		span: ast::TextSpan,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();

		let Some(first) = items.first() else {
			// Nothing but comments — a header-only file, or a `mod` body with
			// something to say and nothing to declare. They are still the
			// list's comments, so they are still emitted.
			self.push_between(
				&mut nodes,
				Before::Opener { from: span.start },
				After::End { at: span.end },
			);
			return self.arena.concat(nodes);
		};

		// The file header, or the line opening a `mod` body. At the top of a
		// file the break this emits has nothing in front of it and disappears.
		self.push_between(
			&mut nodes,
			Before::Opener { from: span.start },
			After::Entry {
				start: first.inner.span.start,
			},
		);

		for (index, item) in items.iter().enumerate() {
			if index > 0 {
				let prev = &items[index - 1];
				let end = prev.inner.span.end;
				// Block-like items always stand apart, however the author
				// spaced them.
				let spaced = prev.inner.inner.is_block_like()
					|| item.inner.inner.is_block_like();
				self.push_between(
					&mut nodes,
					match spaced {
						true => Before::SpacedEntry { end },
						false => Before::Entry { end },
					},
					After::Entry {
						start: item.inner.span.start,
					},
				);
			}
			let id = self.build_item(&item.inner.inner, item.inner.span);
			nodes.push(id);
		}

		// Comments after the last item, before the closing `}` or the end of
		// the file. The first of them may still trail the last item's line.
		self.push_between(
			&mut nodes,
			Before::Entry {
				end: items.last().unwrap().inner.span.end,
			},
			After::End { at: span.end },
		);

		self.arena.concat(nodes)
	}

	fn build_item(&mut self, item: &ast::Item, span: ast::TextSpan) -> NodeId {
		match item {
			ast::Item::Function {
				signature,
				block,
				attributes,
				pub_span,
				..
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut items, attributes);
				if pub_span.is_some() {
					items.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut items, signature);
				items.push(self.text(Text::Space));
				let body = self.build_fn_body(block);
				items.push(body);
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::Item::FunctionDeclaration {
				pub_span,
				attributes,
				signature,
				..
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut items, attributes);
				if pub_span.is_some() {
					items.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut items, signature);
				items.push(self.text(Text::Semi));
				self.arena.concat(items)
			}
			ast::Item::Global {
				pub_span,
				mut_span,
				name,
				ty: type_annotation,
				value,
				attributes,
				..
			} => self.build_global_definition(
				*pub_span,
				*mut_span,
				attributes,
				name,
				type_annotation,
				value,
			),
			ast::Item::Export { entries, .. } => {
				self.build_export_definition(span, entries)
			}
			ast::Item::Import {
				module,
				alias,
				entries,
			} => self.build_import_definition(
				span,
				module,
				alias.as_ref(),
				entries,
			),
			ast::Item::Memory {
				name,
				bound: kind,
				attributes,
				..
			} => {
				let mut parts: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut parts, attributes);
				parts.push(self.text(Text::Memory));
				parts.push(self.symbol(name.inner));
				parts.push(self.text(Text::ColonSp));
				parts.push(self.build_bound_expression(&kind.inner));
				parts.push(self.text(Text::Semi));
				self.arena.concat(parts)
			}
			ast::Item::Enum {
				pub_span,
				attributes,
				repr,
				name,
				variants,
				..
			} => self.build_enum_definition(
				span, *pub_span, attributes, repr, name, variants,
			),
			ast::Item::InherentImpl {
				type_params,
				target,
				items,
				..
			} => self.build_impl_definition(span, type_params, target, items),
			ast::Item::TraitImpl {
				type_params,
				trait_name,
				target,
				items,
				..
			} => self.build_impl_trait_definition(
				span,
				type_params,
				trait_name,
				target,
				items,
			),
			ast::Item::Const {
				pub_span,
				attributes,
				name,
				ty,
				value,
				..
			} => self
				.build_const_definition(*pub_span, attributes, name, ty, value),
			ast::Item::Module {
				pub_span,
				name,
				items,
			} => self.build_module_definition(span, *pub_span, name, items),
			ast::Item::ModuleDeclaration { pub_span, name } => {
				self.build_module_declaration(*pub_span, name)
			}
			ast::Item::Trait {
				pub_span,
				attributes,
				name,
				supertraits,
				items,
				..
			} => self.build_trait_definition(
				span,
				*pub_span,
				attributes,
				name,
				supertraits.as_ref(),
				items,
			),
			ast::Item::Struct {
				id: _,
				attributes,
				name,
				type_params,
				fields,
				pub_span,
			} => self.build_struct_declaration(
				span,
				attributes,
				name,
				type_params,
				fields,
				*pub_span,
			),
			ast::Item::TypeSet {
				pub_span,
				attributes,
				name,
				members,
				..
			} => {
				let mut items: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut items, attributes);
				if pub_span.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Typeset));
				items.push(self.symbol(name.inner));
				items.push(self.text(Text::SpaceLBraceSpace));
				for (i, m) in members.iter().enumerate() {
					if i > 0 {
						items.push(self.text(Text::CommaSp));
					}
					let ty = self.build_type_expression(&m.inner.inner);
					items.push(ty);
				}
				items.push(self.text(Text::SpaceRBrace));
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::Item::TypeAlias {
				pub_span,
				name,
				type_params,
				body,
				attributes,
				..
			} => self.build_type_alias_definition(
				*pub_span,
				name,
				type_params,
				body.as_deref(),
				attributes,
			),
			ast::Item::Use { tree, pub_span } => {
				let mut items: Vec<NodeId> = Vec::new();
				if pub_span.is_some() {
					items.push(self.text(Text::Pub));
				}
				items.push(self.text(Text::Use));
				let tree = self.build_use_tree(&tree.inner);
				items.push(tree);
				items.push(self.text(Text::Semi));
				self.arena.concat(items)
			}
		}
	}

	/// A `use` tree, rendered on one line. Groups stay inline rather than
	/// breaking like an `export` block does: a `use` names things that live
	/// elsewhere, so its length tracks the path being imported rather than
	/// the size of anything in this file, and it stays short in practice.
	fn build_use_tree(&mut self, tree: &ast::UseTree) -> NodeId {
		match tree {
			ast::UseTree::Glob => self.text(Text::Star),
			ast::UseTree::Name { name, alias, .. } => {
				let mut items: Vec<NodeId> = vec![self.symbol(name.inner)];
				if let Some(alias) = alias {
					items.push(self.text(Text::As));
					items.push(self.symbol(alias.inner));
				}
				self.arena.concat(items)
			}
			ast::UseTree::Path { segment, rest } => {
				let segment = self.symbol(segment.inner);
				let colons = self.text(Text::ColonColon);
				let rest = self.build_use_tree(&rest.inner);
				self.arena.concat(vec![segment, colons, rest])
			}
			ast::UseTree::Group(elements) => {
				let mut items: Vec<NodeId> = vec![self.text(Text::LBrace)];
				for (index, element) in elements.iter().enumerate() {
					if index > 0 {
						items.push(self.text(Text::CommaSp));
					}
					let element = self.build_use_tree(&element.inner.inner);
					items.push(element);
				}
				items.push(self.text(Text::RBrace));
				self.arena.concat(items)
			}
		}
	}

	fn build_import_definition(
		&mut self,
		span: ast::TextSpan,
		module: &ast::Spanned<SymbolU32>,
		alias: Option<&ast::Spanned<SymbolU32>>,
		entries: &[ast::Separated<ast::Spanned<ast::ImportEntry>>],
	) -> NodeId {
		let mut items: Vec<NodeId> =
			vec![self.text(Text::Import), self.symbol(module.inner)];

		if let Some(alias) = alias {
			items.push(self.text(Text::As));
			items.push(self.symbol(alias.inner));
		}

		items.push(self.text(Text::SpaceLBrace));

		if entries.is_empty() {
			self.build_empty_braced_comments(&mut items, span);
		} else {
			let last_end = entries.last().unwrap().inner.span.end;

			let mut entry_items: Vec<NodeId> = Vec::new();
			self.push_between(
				&mut entry_items,
				Before::Opener { from: span.start },
				After::Entry {
					start: entries[0].inner.span.start,
				},
			);

			for (index, entry) in entries.iter().enumerate() {
				if index > 0 {
					self.push_between(
						&mut entry_items,
						Before::Entry {
							end: entries[index - 1].inner.span.end,
						},
						After::Entry {
							start: entry.inner.span.start,
						},
					);
				}

				let mut entry_nodes: Vec<NodeId> = Vec::new();

				if let Some(ext_name) = &entry.inner.inner.external_name {
					entry_nodes.push(self.symbol(ext_name.inner));
					entry_nodes.push(self.text(Text::ColonSp));
				}

				match &entry.inner.inner.declaration {
					ast::ImportDeclaration::Function { signature, .. } => {
						self.build_function_signature(
							&mut entry_nodes,
							signature,
						);
						let concat = self.arena.concat(entry_nodes);
						let group = self.arena.group(concat);
						entry_nodes = vec![group];
					}
					ast::ImportDeclaration::Global {
						mut_span,
						name,
						ty,
						..
					} => {
						entry_nodes.push(self.text(Text::Global));
						if mut_span.is_some() {
							entry_nodes.push(self.text(Text::Mut));
						}
						entry_nodes.push(self.symbol(name.inner));
						entry_nodes.push(self.text(Text::ColonSp));
						entry_nodes.push(self.build_type_expression(&ty.inner));
					}
					ast::ImportDeclaration::Memory { name, kind, .. } => {
						entry_nodes.push(self.text(Text::Memory));
						entry_nodes.push(self.symbol(name.inner));
						entry_nodes.push(self.text(Text::ColonSp));
						entry_nodes
							.push(self.build_bound_expression(&kind.inner));
					}
				}

				if entry.separator.is_some() {
					entry_nodes.push(self.text(Text::Semi));
				}

				let entry_concat = self.arena.concat(entry_nodes);
				entry_items.push(entry_concat);
			}

			self.push_between(
				&mut entry_items,
				Before::Entry { end: last_end },
				After::End { at: span.end },
			);

			let concat = self.arena.concat(entry_items);
			let indented = self.arena.indent(concat);
			items.push(indented);
			items.push(self.line());
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(items)
	}

	fn build_module_definition(
		&mut self,
		span: ast::TextSpan,
		pub_span: Option<ast::TextSpan>,
		name: &ast::Spanned<SymbolU32>,
		items: &[ast::Separated<ast::Spanned<ast::Item>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Module));
		nodes.push(self.symbol(name.inner));
		nodes.push(self.text(Text::SpaceLBrace));

		if !items.is_empty() {
			// The body opens its own line: the gap before its first item is
			// where a comment written after `mod name {` belongs.
			let body = self.build_item_list(items, span);
			nodes.push(self.arena.indent(body));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		let concat = self.arena.concat(nodes);
		self.arena.group(concat)
	}

	fn build_module_declaration(
		&mut self,
		pub_span: Option<ast::TextSpan>,
		name: &ast::Spanned<SymbolU32>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Module));
		nodes.push(self.symbol(name.inner));
		nodes.push(self.text(Text::Semi));
		self.arena.concat(nodes)
	}

	fn build_impl_definition(
		&mut self,
		span: ast::TextSpan,
		type_params: &[ast::TypeParam],
		target: &ast::Spanned<ast::TypeExpression>,
		items: &[ast::Separated<ast::Spanned<ast::ImplItem>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = vec![self.text(Text::Impl)];
		self.build_type_params(&mut nodes, type_params);
		nodes.push(self.text(Text::Space));
		nodes.push(self.build_type_expression(&target.inner));
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
		let concat = self.arena.concat(nodes);
		self.arena.group(concat)
	}

	fn build_impl_trait_definition(
		&mut self,
		span: ast::TextSpan,
		type_params: &[ast::TypeParam],
		trait_name: &[ast::PathSegment],
		target: &ast::Spanned<ast::TypeExpression>,
		items: &[ast::Separated<ast::Spanned<ast::ImplItem>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = vec![self.text(Text::Impl)];
		self.build_type_params(&mut nodes, type_params);
		nodes.push(self.text(Text::Space));
		let trait_id = self.build_path_segments(trait_name);
		let for_kw = self.text(Text::ForKw);
		let target_id = self.build_type_expression(&target.inner);
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
		let concat = self.arena.concat(nodes);
		self.arena.group(concat)
	}

	fn build_impl_item_list(
		&mut self,
		span: ast::TextSpan,
		items: &[ast::Separated<ast::Spanned<ast::ImplItem>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		let Some(first) = items.first() else {
			return self.arena.concat(nodes);
		};

		self.push_between(
			&mut nodes,
			Before::Opener { from: span.start },
			After::Entry {
				start: first.inner.span.start,
			},
		);

		for (index, item) in items.iter().enumerate() {
			if index > 0 {
				self.push_between(
					&mut nodes,
					// Impl members always stand apart.
					Before::SpacedEntry {
						end: items[index - 1].inner.span.end,
					},
					After::Entry {
						start: item.inner.span.start,
					},
				);
			}
			nodes.push(self.build_impl_item(&item.inner.inner));
		}

		self.push_between(
			&mut nodes,
			Before::Entry {
				end: items.last().unwrap().inner.span.end,
			},
			After::End { at: span.end },
		);
		self.arena.concat(nodes)
	}

	fn build_impl_item(&mut self, item: &ast::ImplItem) -> NodeId {
		match item {
			ast::ImplItem::Function {
				pub_span,
				attributes,
				signature,
				block,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut nodes, attributes);
				if pub_span.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				self.build_function_signature(&mut nodes, signature);
				nodes.push(self.text(Text::Space));
				nodes.push(self.build_fn_body(block));
				let concat = self.arena.concat(nodes);
				self.arena.group(concat)
			}
			ast::ImplItem::Constant {
				pub_span,
				attributes,
				name,
				ty,
				value,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut nodes, attributes);
				if pub_span.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				nodes.push(self.text(Text::Const));
				nodes.push(self.symbol(name.inner));
				if let Some(ty) = ty {
					nodes.push(self.text(Text::ColonSp));
					nodes.push(self.build_type_expression(&ty.inner));
				}
				nodes.push(self.text(Text::EqSp));
				nodes.push(self.build_expression(value));
				nodes.push(self.text(Text::Semi));
				self.arena.concat(nodes)
			}
			ast::ImplItem::AssocType {
				pub_span, name, ty, ..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				if pub_span.is_some() {
					nodes.push(self.text(Text::Pub));
				}
				nodes.push(self.text(Text::TypeKw));
				nodes.push(self.symbol(name.inner));
				nodes.push(self.text(Text::EqSp));
				nodes.push(self.build_type_expression(&ty.inner));
				nodes.push(self.text(Text::Semi));
				self.arena.concat(nodes)
			}
		}
	}

	fn build_trait_definition(
		&mut self,
		span: ast::TextSpan,
		pub_span: Option<ast::TextSpan>,
		attributes: &[ast::Attribute],
		name: &ast::Spanned<SymbolU32>,
		supertraits: Option<&ast::Spanned<ast::BoundExpression>>,
		items: &[ast::Separated<ast::Spanned<ast::TraitItem>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut nodes, attributes);
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Trait));
		nodes.push(self.symbol(name.inner));

		if let Some(spanned) = supertraits {
			nodes.push(self.text(Text::ColonSp));
			nodes.push(self.build_bound_expression(&spanned.inner));
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
		let concat = self.arena.concat(nodes);
		self.arena.group(concat)
	}

	fn build_trait_item_list(
		&mut self,
		span: ast::TextSpan,
		items: &[ast::Separated<ast::Spanned<ast::TraitItem>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		let Some(first) = items.first() else {
			return self.arena.concat(nodes);
		};

		self.push_between(
			&mut nodes,
			Before::Opener { from: span.start },
			After::Entry {
				start: first.inner.span.start,
			},
		);

		for (index, item) in items.iter().enumerate() {
			if index > 0 {
				self.push_between(
					&mut nodes,
					// Trait members always stand apart, like impl members.
					Before::SpacedEntry {
						end: items[index - 1].inner.span.end,
					},
					After::Entry {
						start: item.inner.span.start,
					},
				);
			}
			nodes.push(self.build_trait_item(&item.inner.inner));
		}

		self.push_between(
			&mut nodes,
			Before::Entry {
				end: items.last().unwrap().inner.span.end,
			},
			After::End { at: span.end },
		);
		self.arena.concat(nodes)
	}

	fn build_trait_item(&mut self, item: &ast::TraitItem) -> NodeId {
		match item {
			ast::TraitItem::Function {
				attributes,
				signature,
				body,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut nodes, attributes);
				self.build_function_signature(&mut nodes, signature);
				match body {
					Some(body) => {
						nodes.push(self.text(Text::Space));
						nodes.push(self.build_fn_body(body));
						let concat = self.arena.concat(nodes);
						self.arena.group(concat)
					}
					None => {
						nodes.push(self.text(Text::Semi));
						self.arena.concat(nodes)
					}
				}
			}
			ast::TraitItem::Const {
				name,
				ty,
				attributes,
				value,
				..
			} => {
				let mut nodes: Vec<NodeId> = Vec::new();
				self.build_attributes(&mut nodes, attributes);
				nodes.push(self.text(Text::Const));
				nodes.push(self.symbol(name.inner));
				nodes.push(self.text(Text::ColonSp));
				nodes.push(self.build_type_expression(&ty.inner));
				if let Some(value) = value {
					nodes.push(self.text(Text::EqSp));
					nodes.push(self.build_expression(value));
				}
				nodes.push(self.text(Text::Semi));
				self.arena.concat(nodes)
			}
			ast::TraitItem::AssociatedType { name, bounds, .. } => {
				let mut nodes: Vec<NodeId> =
					vec![self.text(Text::TypeKw), self.symbol(name.inner)];
				if let Some(b) = bounds {
					nodes.push(self.text(Text::ColonSp));
					nodes.push(self.build_bound_expression(&b.inner));
				}
				nodes.push(self.text(Text::Semi));
				self.arena.concat(nodes)
			}
		}
	}

	fn build_const_definition(
		&mut self,
		pub_span: Option<ast::TextSpan>,
		attributes: &[ast::Attribute],
		name: &ast::Spanned<SymbolU32>,
		ty: &Option<Box<ast::Spanned<ast::TypeExpression>>>,
		value: &ast::Spanned<ast::Expression>,
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut nodes, attributes);
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Const));
		nodes.push(self.symbol(name.inner));
		if let Some(ty) = ty {
			nodes.push(self.text(Text::ColonSp));
			nodes.push(self.build_type_expression(&ty.inner));
		}
		nodes.push(self.text(Text::EqSp));
		nodes.push(self.build_expression(value));
		nodes.push(self.text(Text::Semi));
		self.arena.concat(nodes)
	}

	fn build_type_alias_definition(
		&mut self,
		pub_span: Option<ast::TextSpan>,
		name: &ast::Spanned<SymbolU32>,
		type_params: &[ast::TypeParam],
		body: Option<&ast::Spanned<ast::TypeExpression>>,
		attributes: &[ast::Attribute],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut nodes, attributes);
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::TypeKw));
		nodes.push(self.symbol(name.inner));
		self.build_type_params(&mut nodes, type_params);
		if let Some(body) = body {
			nodes.push(self.text(Text::EqSp));
			nodes.push(self.build_type_expression(&body.inner));
		}
		nodes.push(self.text(Text::Semi));
		self.arena.concat(nodes)
	}

	fn build_match_expression(
		&mut self,
		span: ast::TextSpan,
		scrutinee: &ast::Spanned<ast::Expression>,
		arms: &[ast::Separated<ast::Spanned<ast::MatchArm>>],
	) -> NodeId {
		let match_kw = self.text(Text::Match);
		let scrutinee_id = self.build_expression(scrutinee);
		let mut nodes: Vec<NodeId> =
			vec![match_kw, scrutinee_id, self.text(Text::SpaceLBrace)];

		if !arms.is_empty() {
			let mut arm_items: Vec<NodeId> = Vec::new();
			for (index, arm) in arms.iter().enumerate() {
				self.push_between(
					&mut arm_items,
					match index {
						0 => Before::Opener { from: span.start },
						_ => Before::Entry {
							end: arms[index - 1].inner.span.end,
						},
					},
					After::Entry {
						start: arm.inner.span.start,
					},
				);
				let mut an: Vec<NodeId> =
					vec![self.build_expression(&arm.inner.inner.pattern)];
				an.push(self.text(Text::Arrow));
				an.push(self.build_expression(&arm.inner.inner.body));
				if index + 1 < arms.len() {
					an.push(self.text(Text::Comma));
				} else {
					an.push(self.if_break_comma());
				}
				arm_items.push(self.arena.concat(an));
			}
			self.push_between(
				&mut arm_items,
				Before::Entry {
					end: arms.last().unwrap().inner.span.end,
				},
				After::End { at: span.end },
			);

			let concat = self.arena.concat(arm_items);
			nodes.push(self.arena.indent(concat));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		self.arena.concat(nodes)
	}

	fn build_enum_definition(
		&mut self,
		span: ast::TextSpan,
		pub_span: Option<ast::TextSpan>,
		attributes: &[ast::Attribute],
		repr: &Option<Box<ast::Spanned<ast::TypeExpression>>>,
		name: &ast::Spanned<SymbolU32>,
		variants: &[ast::Separated<ast::Spanned<ast::EnumVariant>>],
	) -> NodeId {
		let mut nodes: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut nodes, attributes);
		if pub_span.is_some() {
			nodes.push(self.text(Text::Pub));
		}
		nodes.push(self.text(Text::Enum));
		nodes.push(self.symbol(name.inner));
		if let Some(repr) = repr {
			nodes.push(self.text(Text::ColonSp));
			nodes.push(self.build_type_expression(&repr.inner));
		}
		nodes.push(self.text(Text::SpaceLBrace));

		if !variants.is_empty() {
			let mut variant_items: Vec<NodeId> = Vec::new();
			for (index, variant) in variants.iter().enumerate() {
				self.push_between(
					&mut variant_items,
					match index {
						0 => Before::Opener { from: span.start },
						_ => Before::Entry {
							end: variants[index - 1].inner.span.end,
						},
					},
					After::Entry {
						start: variant.inner.span.start,
					},
				);
				let mut vn: Vec<NodeId> =
					vec![self.symbol(variant.inner.inner.name.inner)];
				if let Some(value) = &variant.inner.inner.value {
					vn.push(self.text(Text::EqSp));
					vn.push(self.build_expression(value));
				}
				if index + 1 < variants.len() {
					vn.push(self.text(Text::Comma));
				} else {
					vn.push(self.if_break_comma());
				}
				variant_items.push(self.arena.concat(vn));
			}
			self.push_between(
				&mut variant_items,
				Before::Entry {
					end: variants.last().unwrap().inner.span.end,
				},
				After::End { at: span.end },
			);

			let concat = self.arena.concat(variant_items);
			nodes.push(self.arena.indent(concat));
			nodes.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut nodes, span);
		}

		nodes.push(self.text(Text::RBrace));
		self.arena.concat(nodes)
	}

	fn build_struct_declaration(
		&mut self,
		span: ast::TextSpan,
		attributes: &[ast::Attribute],
		name: &ast::Spanned<SymbolU32>,
		type_params: &[ast::TypeParam],
		fields: &[ast::Separated<ast::Spanned<ast::StructField>>],
		pub_span: Option<ast::TextSpan>,
	) -> NodeId {
		let mut items: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut items, attributes);
		if pub_span.is_some() {
			items.push(self.text(Text::Pub));
		}
		items.push(self.text(Text::Struct));
		items.push(self.symbol(name.inner));
		self.build_type_params(&mut items, type_params);
		items.push(self.text(Text::SpaceLBrace));

		if !fields.is_empty() {
			let mut field_items: Vec<NodeId> = Vec::new();
			for (index, field) in fields.iter().enumerate() {
				self.push_between(
					&mut field_items,
					match index {
						0 => Before::Opener { from: span.start },
						_ => Before::Entry {
							end: fields[index - 1].inner.span.end,
						},
					},
					After::Entry {
						start: field.inner.span.start,
					},
				);
				let mut fn_: Vec<NodeId> = Vec::new();
				if field.inner.inner.pub_span.is_some() {
					fn_.push(self.text(Text::Pub));
				}
				fn_.push(self.symbol(field.inner.inner.name.inner));
				fn_.push(self.text(Text::ColonSp));
				fn_.push(
					self.build_type_expression(&field.inner.inner.ty.inner),
				);
				fn_.push(self.text(Text::Comma));
				field_items.push(self.arena.concat(fn_));
			}
			self.push_between(
				&mut field_items,
				Before::Entry {
					end: fields.last().unwrap().inner.span.end,
				},
				After::End { at: span.end },
			);

			let concat = self.arena.concat(field_items);
			items.push(self.arena.indent(concat));
			items.push(self.hard_line());
		} else {
			self.build_empty_braced_comments(&mut items, span);
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(items)
	}

	fn build_export_definition(
		&mut self,
		span: ast::TextSpan,
		entries: &[ast::Separated<ast::Spanned<ast::ExportEntry>>],
	) -> NodeId {
		let mut items: Vec<NodeId> = vec![self.text(Text::ExportLBrace)];

		if entries.is_empty() {
			self.build_empty_braced_comments(&mut items, span);
		} else {
			let last_end = entries.last().unwrap().inner.span.end;

			let mut entry_items: Vec<NodeId> = Vec::new();
			self.push_between(
				&mut entry_items,
				Before::Opener { from: span.start },
				After::Entry {
					start: entries[0].inner.span.start,
				},
			);

			for (index, entry) in entries.iter().enumerate() {
				if index > 0 {
					self.push_between(
						&mut entry_items,
						Before::Entry {
							end: entries[index - 1].inner.span.end,
						},
						After::Entry {
							start: entry.inner.span.start,
						},
					);
				}

				let mut en: Vec<NodeId> =
					vec![self.symbol(entry.inner.inner.name.inner)];
				if let Some(alias) = &entry.inner.inner.alias {
					en.push(self.text(Text::As));
					en.push(self.symbol(alias.inner));
				}
				if entry.separator.is_some() {
					en.push(self.text(Text::Comma));
				}
				entry_items.push(self.arena.concat(en));
			}

			self.push_between(
				&mut entry_items,
				Before::Entry { end: last_end },
				After::End { at: span.end },
			);

			let concat = self.arena.concat(entry_items);
			items.push(self.arena.indent(concat));
			items.push(self.line());
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(items)
	}

	/// The body of a `{ }` that holds no entries. Only comments can be in
	/// there, and they are the list's like any others: an opener on one side,
	/// the closing brace on the other, which is exactly the fourth combination
	/// `push_between` already covers.
	fn build_empty_braced_comments(
		&mut self,
		items: &mut Vec<NodeId>,
		span: ast::TextSpan,
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
		let inner_concat = self.arena.concat(inner);
		items.push(self.arena.indent(inner_concat));
		items.push(self.hard_line());
	}

	fn build_attributes(
		&mut self,
		out: &mut Vec<NodeId>,
		attributes: &[ast::Attribute],
	) {
		for attr in attributes {
			out.push(self.text(Text::HashLBracket));
			out.push(self.symbol(attr.name.inner));
			match &attr.value {
				ast::AttributeValue::Word => {}
				ast::AttributeValue::NameValue(value) => {
					out.push(self.text(Text::EqSp));
					out.push(self.symbol(value.inner));
				}
				ast::AttributeValue::Args(args) => {
					out.push(self.text(Text::LParen));
					for (index, arg) in args.iter().enumerate() {
						let arg = &arg.inner.inner;
						out.push(self.symbol(arg.name.inner));
						out.push(self.text(Text::EqSp));
						match &arg.value {
							ast::AttributeArgValue::Int(value) => {
								out.push(self.source_text(value.span));
							}
							ast::AttributeArgValue::String(value) => {
								out.push(self.symbol(value.inner));
							}
						}
						if index + 1 < args.len() {
							out.push(self.text(Text::CommaSp));
						}
					}
					out.push(self.text(Text::RParen));
				}
			}
			out.push(self.text(Text::RBracket));
			out.push(self.hard_line());
		}
	}

	fn build_type_params(
		&mut self,
		out: &mut Vec<NodeId>,
		type_params: &[ast::TypeParam],
	) {
		if type_params.is_empty() {
			return;
		}
		let mut nodes: Vec<NodeId> = vec![self.text(Text::Lt)];
		let mut inner: Vec<NodeId> = vec![self.line()];
		for (index, param) in type_params.iter().enumerate() {
			inner.push(self.symbol(param.name.inner));
			if let Some(bounds) = &param.bounds {
				inner.push(self.text(Text::ColonSp));
				inner.push(self.build_bound_expression(&bounds.inner));
			}
			if index + 1 < type_params.len() {
				inner.push(self.text(Text::Comma));
				inner.push(self.soft_line());
			} else {
				inner.push(self.if_break_comma());
			}
		}
		let inner_concat = self.arena.concat(inner);
		nodes.push(self.arena.indent(inner_concat));
		nodes.push(self.line());
		nodes.push(self.text(Text::Gt));
		let concat = self.arena.concat(nodes);
		out.push(self.arena.group(concat));
	}

	fn build_function_signature(
		&mut self,
		out: &mut Vec<NodeId>,
		signature: &ast::FunctionSignature,
	) {
		out.push(self.text(Text::Fn));
		out.push(self.symbol(signature.name.inner));
		self.build_type_params(out, &signature.type_params);
		let mut paren_nodes: Vec<NodeId> = vec![self.text(Text::LParen)];

		if !signature.params.is_empty() {
			let mut params: Vec<NodeId> = vec![self.line()];
			for (index, param) in signature.params.iter().enumerate() {
				if param.inner.inner.mut_span.is_some() {
					params.push(self.text(Text::Mut));
				}
				params.push(self.symbol(param.inner.inner.name.inner));
				if let Some(ty) = &param.inner.inner.ty {
					params.push(self.text(Text::ColonSp));
					params.push(self.build_type_expression(&ty.inner));
				}
				if index + 1 < signature.params.len() {
					params.push(self.text(Text::Comma));
					params.push(self.soft_line());
				} else {
					params.push(self.if_break_comma());
				}
			}
			let params_concat = self.arena.concat(params);
			paren_nodes.push(self.arena.indent(params_concat));
			paren_nodes.push(self.line());
		}

		paren_nodes.push(self.text(Text::RParen));
		let paren_concat = self.arena.concat(paren_nodes);
		out.push(self.arena.group(paren_concat));
		if let Some(result) = &signature.result {
			out.push(self.text(Text::Arrow));
			out.push(self.build_type_expression(&result.inner));
		}
	}

	fn build_global_definition(
		&mut self,
		pub_span: Option<ast::TextSpan>,
		mut_span: Option<ast::TextSpan>,
		attributes: &[ast::Attribute],
		name: &ast::Spanned<SymbolU32>,
		type_annotation: &Option<Box<ast::Spanned<ast::TypeExpression>>>,
		value: &ast::Spanned<ast::Expression>,
	) -> NodeId {
		let mut items: Vec<NodeId> = Vec::new();
		self.build_attributes(&mut items, attributes);
		if pub_span.is_some() {
			items.push(self.text(Text::Pub));
		}
		items.push(self.text(Text::Global));
		if mut_span.is_some() {
			items.push(self.text(Text::Mut));
		}
		items.push(self.symbol(name.inner));
		if let Some(annotation) = type_annotation {
			items.push(self.text(Text::ColonSp));
			items.push(self.build_type_expression(&annotation.inner));
		}
		items.push(self.text(Text::EqSp));
		items.push(self.build_expression(value));
		items.push(self.text(Text::Semi));
		self.arena.concat(items)
	}

	fn build_fn_body(
		&mut self,
		block: &ast::Spanned<ast::Expression>,
	) -> NodeId {
		let statements = block.inner.as_block_statements();
		self.build_block(block.span, statements, true)
	}

	fn build_block(
		&mut self,
		block_span: ast::TextSpan,
		statements: &[ast::Separated<ast::Spanned<ast::Statement>>],
		force_break: bool,
	) -> NodeId {
		let concat =
			self.build_block_content(statements, block_span, force_break);
		self.arena.group(concat)
	}

	/// Whether a block holds any comment at all — the test `if`/`else` uses to
	/// force both its branches to break together, since a `//` comment can
	/// never share a line with the code after it.
	fn block_has_comments(&self, block_span: ast::TextSpan) -> bool {
		!self
			.comments
			.between(block_span.start, block_span.end)
			.is_empty()
	}

	/// Same as `build_block`, but leaves the result ungrouped so a caller can
	/// fold it into a larger group — used by `if`/`else` so the two branches
	/// share one break decision instead of each block deciding on its own.
	fn build_block_content(
		&mut self,
		statements: &[ast::Separated<ast::Spanned<ast::Statement>>],
		block_span: ast::TextSpan,
		force_break: bool,
	) -> NodeId {
		let mut items: Vec<NodeId> = vec![self.text(Text::LBrace)];

		if statements.is_empty() {
			self.build_empty_braced_comments(&mut items, block_span);
		} else {
			let single = !force_break
				&& !self.block_has_comments(block_span)
				&& statements.len() == 1;
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
						start: statements[0].inner.span.start,
					},
				);
			}

			for (index, statement) in statements.iter().enumerate() {
				// The break between two statements is emitted here rather
				// than at the end of the previous turn, so that turn can
				// close its line with `;` and let the gap append whatever
				// comment trails it.
				if index > 0 {
					self.push_between(
						&mut inner,
						Before::Entry {
							end: statements[index - 1].inner.span.end,
						},
						After::Entry {
							start: statement.inner.span.start,
						},
					);
				}
				inner.push(self.build_statement(&statement.inner.inner));
				let needs_semi = if index + 1 == statements.len()
					|| statement.inner.inner.is_block_like()
				{
					statement.separator.is_some()
				} else {
					true
				};
				if needs_semi {
					inner.push(self.text(Text::Semi));
				}
			}

			// Comments after the last statement. The first may still trail
			// its line; the rest stand on their own above the closing brace.
			self.push_between(
				&mut inner,
				Before::Entry {
					end: statements.last().unwrap().inner.span.end,
				},
				After::End { at: block_span.end },
			);

			let inner_concat = self.arena.concat(inner);
			items.push(self.arena.indent(inner_concat));
			items.push(if single {
				self.soft_line()
			} else {
				self.hard_line()
			});
		}

		items.push(self.text(Text::RBrace));
		self.arena.concat(items)
	}

	/// An expression that already introduces its own hard-broken multi-line
	/// layout (a struct literal, or a single-argument call hugging one) —
	/// safe to print attached to whatever precedes it (`(`, `=`, ...)
	/// without wrapping it in an extra `line()`/`indent()` pair.
	///
	/// This matters because `Renderer::measure_flat` stops measuring at the
	/// first hard line it finds and returns the (short) width accumulated so
	/// far, so a `Group` containing a struct literal several calls deep is
	/// always measured as "fits" and rendered `Flat`. `Indent` nodes bump
	/// `self.indent` unconditionally, even in `Flat` mode where their own
	/// `line()`/`soft_line()` renders as nothing — so every such wrapper
	/// still stacks an extra, visually pointless indent level onto the
	/// struct literal's own fields. Skipping the wrapper for huggable values
	/// keeps only the indent the literal adds for itself.
	fn is_huggable(expr: &ast::Expression) -> bool {
		if expr.is_block_like() {
			return true;
		}
		match expr {
			ast::Expression::Call { arguments, .. } => {
				arguments.len() == 1
					&& Self::is_huggable(&arguments[0].inner.inner)
			}
			ast::Expression::MethodCall(mc) => {
				mc.arguments.len() == 1
					&& Self::is_huggable(&mc.arguments[0].inner.inner)
			}
			_ => false,
		}
	}

	fn build_call_args(
		&mut self,
		out: &mut Vec<NodeId>,
		arguments: &[ast::Separated<ast::Spanned<ast::Expression>>],
	) {
		out.push(self.text(Text::LParen));
		if arguments.len() == 1 && Self::is_huggable(&arguments[0].inner.inner)
		{
			out.push(self.build_expression(&arguments[0].inner));
		} else if !arguments.is_empty() {
			let mut arg_nodes: Vec<NodeId> = vec![self.line()];
			for (index, arg) in arguments.iter().enumerate() {
				arg_nodes.push(self.build_expression(&arg.inner));
				if index + 1 < arguments.len() {
					arg_nodes.push(self.text(Text::Comma));
					arg_nodes.push(self.soft_line());
				} else {
					arg_nodes.push(self.if_break_comma());
				}
			}
			let args_concat = self.arena.concat(arg_nodes);
			out.push(self.arena.indent(args_concat));
			out.push(self.line());
		}
		out.push(self.text(Text::RParen));
	}

	fn build_expression(
		&mut self,
		expression: &ast::Spanned<ast::Expression>,
	) -> NodeId {
		match &expression.inner {
			ast::Expression::QualifiedPath { root, segments } => {
				let self_type_node =
					self.build_type_expression(&root.self_type.inner);
				self.build_qualified_path(
					self_type_node,
					Some(&root.trait_path),
					segments,
				)
			}
			ast::Expression::Grouped { inner, segments } => {
				let inner_node = self.build_type_expression(&inner.inner);
				self.build_qualified_path(inner_node, None, segments)
			}
			ast::Expression::Path(path) => self.build_path_segments(path),
			ast::Expression::Binary {
				left,
				operator,
				right,
			} => {
				let mut operands: Vec<&ast::Spanned<ast::Expression>> =
					vec![right, left];
				let mut current = left;
				while let ast::Expression::Binary {
					left: l,
					operator: op,
					right: r,
				} = &current.inner
				{
					if op.inner == operator.inner {
						*operands.last_mut().unwrap() = r;
						operands.push(l);
						current = l;
					} else {
						break;
					}
				}
				operands.reverse();

				let first = self.build_expression(operands[0]);
				let mut parts: Vec<NodeId> = vec![first];
				let op_text = Text::from(operator.inner);
				for operand in &operands[1..] {
					let sl = self.soft_line();
					let op_id = self.text(op_text);
					let sp = self.text(Text::Space);
					let operand_id = self.build_expression(operand);
					let inner = self.arena.concat4(sl, op_id, sp, operand_id);
					parts.push(self.arena.indent(inner));
				}
				let concat = self.arena.concat(parts);
				self.arena.group(concat)
			}
			ast::Expression::Block { statements } => {
				self.build_block(expression.span, statements, false)
			}
			ast::Expression::Unreachable => self.text(Text::Unreachable),
			ast::Expression::True => self.text(Text::True),
			ast::Expression::False => self.text(Text::False),
			ast::Expression::Placeholder => self.text(Text::Underscore),
			ast::Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => {
				let if_kw = self.text(Text::If);
				let cond = self.build_expression(condition);
				let sp = self.text(Text::Space);

				let then_statements = then_block.inner.as_block_statements();
				let else_data = else_block
					.as_deref()
					.map(|b| (b.inner.as_block_statements(), b.span));

				let force_break = then_statements.len() > 1
					|| self.block_has_comments(then_block.span)
					|| else_data.is_some_and(|(statements, span)| {
						statements.len() > 1 || self.block_has_comments(span)
					});

				let then_id = self.build_block_content(
					then_statements,
					then_block.span,
					force_break,
				);
				let mut items: Vec<NodeId> = vec![if_kw, cond, sp, then_id];
				if let Some((statements, span)) = else_data {
					items.push(self.text(Text::Else));
					items.push(self.build_block_content(
						statements,
						span,
						force_break,
					));
				}
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::Expression::Loop { block } => {
				let loop_kw = self.text(Text::Loop);
				let block_id = self.build_expression(block);
				let concat = self.arena.concat2(loop_kw, block_id);
				self.arena.group(concat)
			}
			ast::Expression::Match { scrutinee, arms } => {
				self.build_match_expression(expression.span, scrutinee, arms)
			}
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
				self.arena.concat(items)
			}
			ast::Expression::Return { value } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Return)];
				if let Some(value) = value {
					items.push(self.text(Text::Space));
					items.push(self.build_expression(value));
				}
				self.arena.concat(items)
			}
			ast::Expression::Cast { value, ty } => {
				let val = self.build_expression(value);
				let as_kw = self.text(Text::As);
				let ty_id = self.build_type_expression(&ty.inner);
				self.arena.concat3(val, as_kw, ty_id)
			}
			ast::Expression::Continue { label } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::Continue)];
				if let Some(label) = label {
					items.push(self.text(Text::LabelColon));
					items.push(self.symbol(label.inner));
				}
				self.arena.concat(items)
			}
			ast::Expression::Int { .. } | ast::Expression::Float { .. } => {
				self.source_text(expression.span)
			}
			ast::Expression::Grouping { value } => {
				let open = self.text(Text::LParen);
				let val = self.build_expression(value);
				let close = self.text(Text::RParen);
				self.arena.concat3(open, val, close)
			}
			ast::Expression::Call { callee, arguments } => {
				let callee_id = self.build_expression(callee);
				let mut items: Vec<NodeId> = vec![callee_id];
				self.build_call_args(&mut items, arguments);
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::Expression::MethodCall(mc) => {
				let obj_id = self.build_expression(&mc.object);
				let dot = self.text(Text::Dot);
				let method_sym = self.symbol(mc.method.inner);
				let mut items: Vec<NodeId> = vec![obj_id, dot, method_sym];
				if !mc.type_args.is_empty() {
					items.push(self.text(Text::ColonColonLt));
					for (i, arg) in mc.type_args.iter().enumerate() {
						if i > 0 {
							items.push(self.text(Text::CommaSp));
						}
						items.push(self.build_type_expression(&arg.inner));
					}
					items.push(self.text(Text::Gt));
				}
				self.build_call_args(&mut items, &mc.arguments);
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::Expression::Label { label, block } => {
				let sym = self.symbol(label.inner);
				let colon_sp = self.text(Text::ColonSp);
				let block_id = self.build_expression(block);
				self.arena.concat3(sym, colon_sp, block_id)
			}
			ast::Expression::Error => unreachable!(),
			ast::Expression::Unary { operator, operand } => {
				let op_id = self.text(Text::from(operator.inner));
				let operand_id = self.build_expression(operand);
				self.arena.concat2(op_id, operand_id)
			}
			ast::Expression::String | ast::Expression::Char => {
				self.source_text(expression.span)
			}
			ast::Expression::ObjectAccess { object, member } => {
				let obj_id = self.build_expression(object);
				let dot = self.text(Text::Dot);
				let sym = self.symbol(member.inner);
				self.arena.concat3(obj_id, dot, sym)
			}
			ast::Expression::Deref { pointer } => {
				let ptr_id = self.build_expression(pointer);
				let dot_star = self.text(Text::DotStar);
				self.arena.concat2(ptr_id, dot_star)
			}
			ast::Expression::AddressOf { value } => {
				let val_id = self.build_expression(value);
				let suffix = self.text(Text::DotAmp);
				self.arena.concat2(val_id, suffix)
			}
			ast::Expression::StructInit { path, fields } => {
				let path_id = self.build_path_segments(path);
				let open = self.text(Text::ColonColonLBrace);
				let mut items: Vec<NodeId> = vec![path_id, open];

				let has_block_value = fields.iter().any(|f| {
					f.inner
						.inner
						.value
						.as_ref()
						.is_some_and(|v| v.inner.is_block_like())
				});
				if !fields.is_empty() {
					let field_count = fields.len();
					let sep = if has_block_value {
						self.hard_line()
					} else {
						self.soft_line()
					};
					let mut field_items: Vec<NodeId> = vec![sep];
					for (index, field) in fields.iter().enumerate() {
						field_items
							.push(self.symbol(field.inner.inner.name.inner));
						if let Some(value) = &field.inner.inner.value {
							field_items.push(self.text(Text::ColonSp));
							field_items.push(self.build_expression(value));
						}
						let is_last = index + 1 == field_count;
						if !is_last || has_block_value {
							field_items.push(self.text(Text::Comma));
						} else {
							field_items.push(self.if_break_comma());
						}
						if !is_last {
							field_items.push(if has_block_value {
								self.hard_line()
							} else {
								self.soft_line()
							});
						}
					}

					let concat = self.arena.concat(field_items);
					items.push(self.arena.indent(concat));
					items.push(if has_block_value {
						self.hard_line()
					} else {
						self.soft_line()
					});
				}

				items.push(self.text(Text::RBrace));
				if has_block_value {
					self.arena.concat(items)
				} else {
					let concat = self.arena.concat(items);
					self.arena.group(concat)
				}
			}
			ast::Expression::TypeApplication { callee, args } => {
				let callee_id = self.build_expression(callee);
				let mut items: Vec<NodeId> =
					vec![callee_id, self.text(Text::ColonColonLt)];
				for (i, arg) in args.iter().enumerate() {
					if i > 0 {
						items.push(self.text(Text::CommaSp));
					}
					items.push(self.build_type_expression(&arg.inner));
				}
				items.push(self.text(Text::Gt));
				self.arena.concat(items)
			}
			ast::Expression::ArrayList { elements } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::LBracket)];
				for (i, element) in elements.iter().enumerate() {
					if i > 0 {
						items.push(self.text(Text::CommaSp));
					}
					items.push(self.build_expression(element));
				}
				items.push(self.text(Text::RBracket));
				self.arena.concat(items)
			}
			ast::Expression::ArrayRepeat { value, count } => {
				let open = self.text(Text::LBracket);
				let val = self.build_expression(value);
				let semi_sp = self.text(Text::Semi);
				let sp = self.text(Text::Space);
				let cnt = self.build_expression(count);
				let close = self.text(Text::RBracket);
				self.arena.concat(vec![open, val, semi_sp, sp, cnt, close])
			}
			ast::Expression::Index { object, index } => {
				let obj_id = self.build_expression(object);
				let open = self.text(Text::LBracket);
				let idx = self.build_expression(index);
				let close = self.text(Text::RBracket);
				self.arena.concat4(obj_id, open, idx, close)
			}
			ast::Expression::SliceRange { object, start, end } => {
				let obj_id = self.build_expression(object);
				let mut parts: Vec<NodeId> =
					vec![obj_id, self.text(Text::LBracket)];
				if let Some(s) = start {
					parts.push(self.build_expression(s));
				}
				parts.push(self.text(Text::DotDot));
				if let Some(e) = end {
					parts.push(self.build_expression(e));
				}
				parts.push(self.text(Text::RBracket));
				self.arena.concat(parts)
			}
			ast::Expression::Tuple { elements } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::LParen)];

				if !elements.is_empty() {
					let last_idx = elements.len() - 1;
					let mut element_items: Vec<NodeId> = vec![self.line()];
					for (index, element) in elements.iter().enumerate() {
						let el = self.build_expression(element);
						let mut nodes: Vec<NodeId> = vec![el];
						if index < last_idx || elements.len() == 1 {
							nodes.push(self.text(Text::Comma));
						} else {
							nodes.push(self.if_break_comma());
						}
						element_items.push(self.arena.concat(nodes));
						if index < last_idx {
							element_items.push(self.soft_line());
						}
					}

					let concat = self.arena.concat(element_items);
					items.push(self.arena.indent(concat));
					items.push(self.line());
				}

				items.push(self.text(Text::RParen));
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
		}
	}

	fn build_pattern(&mut self, out: &mut Vec<NodeId>, pattern: &ast::Pattern) {
		match pattern {
			ast::Pattern::Wildcard => out.push(self.text(Text::Underscore)),
			ast::Pattern::Binding { mut_span, name } => {
				if mut_span.is_some() {
					out.push(self.text(Text::Mut));
				}
				out.push(self.symbol(name.inner));
			}
			ast::Pattern::Tuple { elements } => {
				out.push(self.text(Text::LParen));
				for (i, element) in elements.iter().enumerate() {
					if i > 0 {
						out.push(self.text(Text::CommaSp));
					}
					self.build_pattern(out, &element.inner.inner);
				}
				out.push(self.text(Text::RParen));
			}
			ast::Pattern::Struct { path, fields, rest } => {
				out.push(self.build_path_segments(path));
				out.push(self.text(Text::ColonColonLBrace));
				for (i, field) in fields.iter().enumerate() {
					if i > 0 {
						out.push(self.text(Text::CommaSp));
					} else {
						out.push(self.text(Text::Space));
					}
					out.push(self.symbol(field.inner.inner.name.inner));
					if let Some(pat) = &field.inner.inner.pattern {
						out.push(self.text(Text::ColonSp));
						self.build_pattern(out, &pat.inner);
					}
				}
				if rest.is_some() {
					out.push(self.text(if fields.is_empty() {
						Text::Space
					} else {
						Text::CommaSp
					}));
					out.push(self.text(Text::DotDot));
				}
				if !fields.is_empty() || rest.is_some() {
					out.push(self.text(Text::Space));
				}
				out.push(self.text(Text::RBrace));
			}
		}
	}

	fn build_statement(&mut self, statement: &ast::Statement) -> NodeId {
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
				self.build_pattern(&mut items, &pattern.inner);
				if let Some(annotation) = type_annotation {
					items.push(self.text(Text::ColonSp));
					items.push(self.build_type_expression(&annotation.inner));
				}
				let value_node = self.build_expression(value);
				if Self::is_huggable(&value.inner) {
					items.push(self.text(Text::EqSp));
					items.push(value_node);
				} else {
					items.push(self.text(Text::EqBare));
					let sl = self.soft_line();
					let inner = self.arena.concat2(sl, value_node);
					items.push(self.arena.indent(inner));
				}
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
		}
	}

	fn build_path_segments(&mut self, path: &[ast::PathSegment]) -> NodeId {
		let mut items: Vec<NodeId> = Vec::new();
		for (i, seg) in path.iter().enumerate() {
			if i > 0 {
				items.push(self.text(Text::ColonColon));
			}
			items.push(self.symbol(seg.ident.inner));
			if !seg.type_args.is_empty() {
				items.push(self.text(Text::ColonColonLt));
				for (j, arg) in seg.type_args.iter().enumerate() {
					if j > 0 {
						items.push(self.text(Text::CommaSp));
					}
					items.push(self.build_type_expression(&arg.inner));
				}
				items.push(self.text(Text::Gt));
			}
		}
		self.arena.concat(items)
	}

	/// Formats `<self_type_node [as trait_segments]>::segments` — shared by
	/// `QualifiedPath` (`<Type as Trait>::Item`, `trait_segments: Some`) and
	/// `Grouped` (`<Type>::Item`, `trait_segments: None`) in both type
	/// position and expression position, which differ only in how
	/// `self_type_node` itself was built.
	fn build_qualified_path(
		&mut self,
		self_type_node: NodeId,
		trait_segments: Option<&[ast::PathSegment]>,
		segments: &[ast::PathSegment],
	) -> NodeId {
		let mut items: Vec<NodeId> = vec![self.text(Text::Lt), self_type_node];
		if let Some(trait_segments) = trait_segments {
			items.push(self.text(Text::As));
			items.push(self.build_path_segments(trait_segments));
		}
		items.push(self.text(Text::Gt));
		items.push(self.text(Text::ColonColon));
		items.push(self.build_path_segments(segments));
		self.arena.concat(items)
	}

	fn build_bound_expression(
		&mut self,
		bound: &ast::BoundExpression,
	) -> NodeId {
		match bound {
			ast::BoundExpression::Path(segs) => self.build_path_segments(segs),
			ast::BoundExpression::WithBindings { path, bindings } => {
				let base_id = self.build_bound_expression(path);
				let where_kw = self.text(Text::Where);
				let open = self.text(Text::LBraceSpace);
				let close = self.text(Text::SpaceRBrace);
				let mut binding_parts: Vec<NodeId> = Vec::new();
				for (i, binding) in bindings.iter().enumerate() {
					if i > 0 {
						binding_parts.push(self.text(Text::CommaSp));
					}
					let key = self.symbol(binding.name.inner);
					let rhs = match &binding.kind {
						ast::AssocTypeBindingKind::Equals(ty) => {
							let eq = self.text(Text::EqSp);
							let ty = self.build_type_expression(&ty.inner);
							self.arena.concat2(eq, ty)
						}
						ast::AssocTypeBindingKind::Bound(bound) => {
							let colon = self.text(Text::ColonSp);
							let bound =
								self.build_bound_expression(&bound.inner);
							self.arena.concat2(colon, bound)
						}
					};
					binding_parts.push(self.arena.concat2(key, rhs));
				}
				let bindings_concat = self.arena.concat(binding_parts);
				self.arena.concat5(
					base_id,
					where_kw,
					open,
					bindings_concat,
					close,
				)
			}
			ast::BoundExpression::BoundList(items) => {
				let mut parts: Vec<NodeId> = Vec::new();
				for (i, b) in items.iter().enumerate() {
					if i > 0 {
						parts.push(self.text(Text::PlusSp));
					}
					parts.push(self.build_bound_expression(&b.inner));
				}
				self.arena.concat(parts)
			}
		}
	}

	fn build_type_expression(
		&mut self,
		type_expression: &ast::TypeExpression,
	) -> NodeId {
		match type_expression {
			ast::TypeExpression::QualifiedPath { root, segments } => {
				let self_type_node =
					self.build_type_expression(&root.self_type.inner);
				self.build_qualified_path(
					self_type_node,
					Some(&root.trait_path),
					segments,
				)
			}
			ast::TypeExpression::Grouped { inner, segments } => {
				let inner_node = self.build_type_expression(&inner.inner);
				self.build_qualified_path(inner_node, None, segments)
			}
			ast::TypeExpression::Infer => self.text(Text::Underscore),
			ast::TypeExpression::Path(path) => self.build_path_segments(path),
			ast::TypeExpression::Function { params, result } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::FnParen)];

				if !params.is_empty() {
					let mut param_items: Vec<NodeId> = vec![self.line()];
					for (index, param) in params.iter().enumerate() {
						if let Some(name) = &param.inner.inner.name {
							param_items.push(self.symbol(name.inner));
							param_items.push(self.text(Text::ColonSp));
						}
						param_items.push(self.build_type_expression(
							&param.inner.inner.ty.inner,
						));
						if index + 1 < params.len() {
							param_items.push(self.text(Text::Comma));
							param_items.push(self.soft_line());
						} else {
							param_items.push(self.if_break_comma());
						}
					}
					let params_concat = self.arena.concat(param_items);
					items.push(self.arena.indent(params_concat));
					items.push(self.line());
				}

				items.push(self.text(Text::RParen));
				if let Some(result) = result {
					items.push(self.text(Text::Arrow));
					items.push(self.build_type_expression(&result.inner));
				}
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::TypeExpression::Pointer { ownership, inner } => {
				let items: Vec<NodeId> = vec![
					self.text(ownership_sigil(*ownership)),
					self.build_type_expression(&inner.inner),
				];
				self.arena.concat(items)
			}
			ast::TypeExpression::Slice { ownership, inner } => {
				let items: Vec<NodeId> = vec![
					self.text(ownership_sigil(*ownership)),
					self.text(Text::LBracket),
					self.build_type_expression(&inner.inner),
					self.text(Text::RBracket),
				];
				self.arena.concat(items)
			}
			ast::TypeExpression::Array {
				ownership,
				inner,
				size,
			} => {
				let items: Vec<NodeId> = vec![
					self.text(ownership_sigil(*ownership)),
					self.text(Text::LBracket),
					self.build_type_expression(&inner.inner),
					self.text(Text::Semi),
					self.text(Text::Space),
					self.source_text(size.span),
					self.text(Text::RBracket),
				];
				self.arena.concat(items)
			}
			ast::TypeExpression::Tuple { elements } => {
				let mut items: Vec<NodeId> = vec![self.text(Text::LParen)];

				if !elements.is_empty() {
					let last_idx = elements.len() - 1;
					let mut element_items: Vec<NodeId> = vec![self.line()];
					for (index, element) in elements.iter().enumerate() {
						let ty = self.build_type_expression(&element.inner);
						let mut nodes: Vec<NodeId> = vec![ty];
						if index < last_idx || elements.len() == 1 {
							nodes.push(self.text(Text::Comma));
						} else {
							nodes.push(self.if_break_comma());
						}
						element_items.push(self.arena.concat(nodes));
						if index < last_idx {
							element_items.push(self.soft_line());
						}
					}

					let concat = self.arena.concat(element_items);
					items.push(self.arena.indent(concat));
					items.push(self.line());
				}

				items.push(self.text(Text::RParen));
				let concat = self.arena.concat(items);
				self.arena.group(concat)
			}
			ast::TypeExpression::MemoryTagged { memory, inner } => {
				let mem_id = self.build_path_segments(memory);
				let sep = self.text(Text::ColonColon);
				let ty = self.build_type_expression(&inner.inner);
				self.arena.concat3(mem_id, sep, ty)
			}
			ast::TypeExpression::GenericApplication { name, args } => {
				let mut inner_parts: Vec<NodeId> = Vec::new();
				for (i, sep) in args.iter().enumerate() {
					if i > 0 {
						inner_parts.push(self.text(Text::CommaSp));
					}
					inner_parts
						.push(self.build_type_expression(&sep.inner.inner));
				}
				let name_sym = self.symbol(name.inner);
				let open = self.text(Text::Lt);
				let inner_concat = self.arena.concat(inner_parts);
				let close = self.text(Text::Gt);
				self.arena.concat4(name_sym, open, inner_concat, close)
			}
		}
	}
}

#[derive(Clone, Copy)]
pub struct RendererConfig {
	pub max_line_width: u32,
	pub indent_width: u8,
	pub trailing_comma: bool,
}

impl Default for RendererConfig {
	fn default() -> Self {
		Self {
			max_line_width: 80,
			indent_width: 4,
			trailing_comma: true,
		}
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
		}
	}

	fn render(mut self, root: NodeId) -> String {
		self.render_node(root, RenderMode::Break);
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
		self.buffer.push('\n');
	}

	/// Ends the current line and opens the next one at the current indent.
	///
	/// TODO: `" ".repeat` heap-allocates a `String` per line break, and every
	/// broken line goes through here — thousands of throwaway allocations per
	/// file. A `push_str` from a static run of spaces (looping only for an
	/// indent deeper than it) writes the same bytes with none. Left with the
	/// arena TODO above; neither is worth doing until the formatter is
	/// somewhere that its speed is felt.
	fn newline_indented(&mut self) {
		self.newline();
		self.buffer.push_str(&" ".repeat(self.indent));
		self.position = self.indent;
	}

	fn render_node(&mut self, id: NodeId, mode: RenderMode) {
		match self.arena.nodes[id as usize] {
			Node::Text(t) => {
				let s = t.as_str();
				self.buffer.push_str(s);
				self.position += s.len();
			}
			Node::SourceText(span) => {
				let text = span.extract_str(self.source);
				self.buffer.push_str(text);
				self.position += text.len();
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
				for i in start as usize..(start + len) as usize {
					self.render_node(self.arena.children[i], mode);
				}
			}
			Node::Group(inner_id) => {
				let mode = if self.measure_flat(id)
					<= (self.config.max_line_width as usize)
						.saturating_sub(self.position)
				{
					RenderMode::Flat
				} else {
					RenderMode::Break
				};
				self.render_node(inner_id, mode);
			}
			Node::Indent(inner_id) => {
				self.indent += self.config.indent_width as usize;
				self.render_node(inner_id, mode);
				self.indent -= self.config.indent_width as usize;
			}
			Node::IfBreakComma => match mode {
				RenderMode::Flat => {}
				RenderMode::Break => {
					self.buffer.push(',');
					self.position += 1;
				}
			},
		}
	}

	fn measure_flat(&self, id: NodeId) -> usize {
		let mut width = 0usize;
		let mut stack: Vec<NodeId> = vec![id];
		while let Some(current_id) = stack.pop() {
			match self.arena.nodes[current_id as usize] {
				Node::Text(t) => width += t.as_str().len(),
				Node::SourceText(span) => {
					width += (span.end - span.start) as usize
				}
				Node::Symbol { len, .. } => width += len as usize,
				Node::SoftLine => width += 1,
				Node::Line | Node::IfBreakComma => {}
				Node::BlankLine | Node::HardLine => return width,
				Node::Group(inner) | Node::Indent(inner) => stack.push(inner),
				Node::Concat { start, len } => {
					for i in (start as usize..(start + len) as usize).rev() {
						stack.push(self.arena.children[i]);
					}
				}
			}
		}
		width
	}
}

fn ownership_sigil(ownership: ast::Ownership) -> Text {
	match ownership {
		ast::Ownership::Exclusive => Text::Star,
		ast::Ownership::Shared => Text::Amp,
	}
}

pub fn format(
	ast: &ast::AST,
	interner: &ast::StringInterner,
	source: &str,
	config: RendererConfig,
) -> String {
	let mut builder = Builder {
		interner,
		source,
		comments: &ast.comments,
		arena: Arena::new(),
	};
	let body = builder.build(ast);
	let hl = builder.hard_line();
	let root = builder.arena.concat2(body, hl);
	let Builder { arena, .. } = builder;
	Renderer::new(config, interner, source, &arena).render(root)
}
