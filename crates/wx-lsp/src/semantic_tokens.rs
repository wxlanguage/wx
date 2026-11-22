//! Semantic tokens: what each written name in a file means, as the client's
//! token types and modifiers.
//!
//! Every token is a name the compiler resolved (`Semantics::resolutions_in`)
//! or a name a declaration introduces (`Snapshot::definitions_in`). Nothing
//! else is a token: literals, operators, the keywords that name nothing and
//! names that did not resolve are left to the editor's grammar. Where one
//! name is both (a shorthand field pattern `P({ x })` reads the field and
//! binds `x`), the declaration is what it means.
//!
//! A name written as a keyword (`self`, `Self`, `super`, `package`) is a
//! `keyword` token whatever it resolves to: keywords are reserved, so the
//! spelling alone says it is one, and the token keeps the theme's keyword
//! colour on it whatever the editor's grammar knows.
//!
//! The legend is standard LSP only, so every theme colours it.

use codespan_reporting::files::Files as _;
use tower_lsp_server::ls_types::{
	Position, Range, SemanticToken, SemanticTokenModifier, SemanticTokenType,
	SemanticTokensLegend,
};
use wx_compiler::diagnostics::TextSpan;
use wx_compiler::symbols::Keyword;
use wx_compiler::tir::{
	BodyOwner, DeclKind, Definition, FunctionIdx, MemberKind, Reference,
};
use wx_compiler::vfs::{FileId, Files};

use crate::convert::{byte_offset_to_utf16_offset, position_to_offset};
use crate::query;
use crate::snapshot::Snapshot;

/// The token types, in legend order: a token's type is its index here.
#[derive(Clone, Copy)]
enum TokenType {
	Namespace,
	Type,
	Struct,
	Enum,
	Interface,
	TypeParameter,
	Parameter,
	Variable,
	Property,
	EnumMember,
	Function,
	Method,
	Keyword,
}

const TOKEN_TYPES: &[SemanticTokenType] = &[
	SemanticTokenType::NAMESPACE,
	SemanticTokenType::TYPE,
	SemanticTokenType::STRUCT,
	SemanticTokenType::ENUM,
	SemanticTokenType::INTERFACE,
	SemanticTokenType::TYPE_PARAMETER,
	SemanticTokenType::PARAMETER,
	SemanticTokenType::VARIABLE,
	SemanticTokenType::PROPERTY,
	SemanticTokenType::ENUM_MEMBER,
	SemanticTokenType::FUNCTION,
	SemanticTokenType::METHOD,
	SemanticTokenType::KEYWORD,
];

/// The token modifiers, in legend order: modifier `i` is bit `1 << i`.
const TOKEN_MODIFIERS: &[SemanticTokenModifier] = &[
	SemanticTokenModifier::DECLARATION,
	SemanticTokenModifier::READONLY,
	SemanticTokenModifier::STATIC,
	SemanticTokenModifier::MODIFICATION,
	SemanticTokenModifier::DEFAULT_LIBRARY,
];

const DECLARATION: u32 = 1 << 0;
const READONLY: u32 = 1 << 1;
const STATIC: u32 = 1 << 2;
/// A local or a field declared `mut`, where it is declared and wherever it is
/// named, as rust-analyzer marks a mutable binding.
const MODIFICATION: u32 = 1 << 3;
/// Provided by the compiler rather than defined in wx: an intrinsic (a
/// function core leaves to the compiler), a primitive type or a literal kind
/// (`Semantics::is_compiler_provided`). A core function with a body is an
/// ordinary function.
const DEFAULT_LIBRARY: u32 = 1 << 4;

pub(crate) fn legend() -> SemanticTokensLegend {
	SemanticTokensLegend {
		token_types: TOKEN_TYPES.to_vec(),
		token_modifiers: TOKEN_MODIFIERS.to_vec(),
	}
}

/// The tokens of `file`, delta-encoded as the protocol sends them; only
/// those that overlap `range` when one is given.
pub(crate) fn tokens(
	snapshot: &Snapshot,
	file: FileId,
	range: Option<Range>,
) -> Option<Vec<SemanticToken>> {
	let files = &snapshot.compilation.files;
	let source = files.get(file).ok()?.source.as_str();
	let range = match range {
		Some(range) => {
			let start = position_to_offset(files, file, range.start)?;
			let end = position_to_offset(files, file, range.end)?;
			Some(TextSpan { start, end })
		}
		None => None,
	};
	let wanted = |span: TextSpan| {
		range.is_none_or(|range| {
			span.start <= range.end && range.start <= span.end
		})
	};
	let written = |span: TextSpan| {
		source
			.get(usize::from(span.start)..usize::from(span.end))
			.unwrap_or("")
	};

	// The uses and the declarations, each in source order, merged into one
	// stream; a declaration wins at a name that is both.
	let mut uses = query::resolutions_in(&snapshot.references, file)
		.map(|(span, reference)| (span.span, reference))
		.peekable();
	let mut declarations = snapshot
		.definitions_in(file)
		.map(|(span, definition)| (span.span, definition))
		.peekable();
	let names = std::iter::from_fn(|| {
		let declared = declarations.peek().map(|&(span, _)| span);
		if uses.peek().is_some_and(|&(at, _)| {
			declared.is_none_or(|declared| at < declared)
		}) {
			let (span, reference) = uses.next()?;
			return Some((span, Name::Use(reference)));
		}
		let (span, definition) = declarations.next()?;
		uses.next_if(|&(at, _)| at == span);
		Some((span, Name::Declaration(definition)))
	});

	let mut data = Vec::new();
	let mut cursor = Cursor::default();
	let (mut line, mut character) = (0, 0);
	for (span, name) in names {
		if !wanted(span) {
			continue;
		}
		let token = match name {
			Name::Use(reference) => {
				token(snapshot, reference.definition(), written(span), 0)
			}
			Name::Declaration(definition) => {
				token(snapshot, definition, written(span), DECLARATION)
			}
		};
		let Some((kind, modifiers)) = token else {
			continue;
		};
		let position =
			cursor.advance(files, file, source, usize::from(span.start))?;
		let delta_line = position.line - line;
		data.push(SemanticToken {
			delta_line,
			delta_start: if delta_line == 0 {
				position.character - character
			} else {
				position.character
			},
			// A name never spans lines, so its length is its own UTF-16
			// length.
			length: byte_offset_to_utf16_offset(written(span)) as u32,
			token_type: kind as u32,
			token_modifiers_bitset: modifiers,
		});
		(line, character) = (position.line, position.character);
	}
	Some(data)
}

/// A written name: a use the compiler resolved, or a declaration.
enum Name {
	Use(Reference),
	Declaration(Definition),
}

/// The position of the last token, carried forward: tokens come in source
/// order, so each counts only the text since the one before it, and looks
/// its line up only when it starts on a later one.
#[derive(Default)]
struct Cursor {
	/// The byte offset of the last token's start.
	at: usize,
	line: u32,
	/// The byte offset its line ends at, where the next one starts.
	line_end: usize,
	character: u32,
}

impl Cursor {
	fn advance(
		&mut self,
		files: &Files,
		file: FileId,
		source: &str,
		offset: usize,
	) -> Option<Position> {
		if offset >= self.line_end {
			let line = files.line_index(file, offset).ok()?;
			let range = files.line_range(file, line).ok()?;
			self.line = line as u32;
			self.line_end = range.end;
			self.at = range.start;
			self.character = 0;
		}
		self.character +=
			byte_offset_to_utf16_offset(source.get(self.at..offset)?) as u32;
		self.at = offset;
		Some(Position {
			line: self.line,
			character: self.character,
		})
	}
}

/// The token of a name of `definition` written as `written`, with
/// `modifiers` for how it is written there (declared, or written to): a
/// keyword, which has no modifiers, or what `classify` makes of the
/// definition. `None` for a name that is not coloured.
fn token(
	snapshot: &Snapshot,
	definition: Definition,
	written: &str,
	modifiers: u32,
) -> Option<(TokenType, u32)> {
	if Keyword::try_from(written).is_ok() {
		return Some((TokenType::Keyword, 0));
	}
	let (kind, own) = classify(snapshot, definition)?;
	Some((kind, own | modifiers))
}

/// The token type and modifiers of a name of `definition`, whether it
/// declares it or uses it: what the definition is, and `defaultLibrary` for
/// one the compiler provides. `None` for a label, which no standard type
/// fits, and for a package, whose one name that is not a keyword is a
/// package instance's key: a string literal, which the editor's grammar
/// colours.
fn classify(
	snapshot: &Snapshot,
	definition: Definition,
) -> Option<(TokenType, u32)> {
	let sema = &snapshot.sema;
	let decls = &sema.decls;
	let default_library = match query::is_compiler_provided(sema, definition) {
		true => DEFAULT_LIBRARY,
		false => 0,
	};
	let (kind, modifiers) = match definition {
		Definition::Item(key) => match sema.declaration_kind(key) {
			DeclKind::Package(_) => return None,
			DeclKind::Module(_)
			| DeclKind::Import(_)
			| DeclKind::PackageInstance(_) => (TokenType::Namespace, 0),
			DeclKind::Enum(_) => (TokenType::Enum, 0),
			DeclKind::EnumVariant(_) => (TokenType::EnumMember, 0),
			DeclKind::Struct(_) => (TokenType::Struct, 0),
			// A memory is what a pointer type names, as a memory parameter
			// `M: Memory` is a type parameter.
			DeclKind::Memory(_) => (TokenType::Type, 0),
			DeclKind::Trait(_) | DeclKind::TypeSet(_) => {
				(TokenType::Interface, 0)
			}
			DeclKind::Global(index) => {
				let global = &decls.globals[usize::from(index)];
				let readonly = match global.mut_trait_impl_index {
					Some(_) => 0,
					None => READONLY,
				};
				(TokenType::Variable, STATIC | readonly)
			}
			DeclKind::Function(index) => (function(snapshot, index), 0),
			DeclKind::Const(_) => (TokenType::Variable, READONLY),
			DeclKind::AssocType(_) | DeclKind::TypeAlias(_) => {
				(TokenType::Type, 0)
			}
		},
		Definition::Member(
			MemberKind::Function(index) | MemberKind::Method(index),
		) => (function(snapshot, index), 0),
		Definition::Member(MemberKind::Constant(_)) => {
			(TokenType::Variable, READONLY)
		}
		Definition::Member(MemberKind::AssociatedType(_)) => {
			(TokenType::Type, 0)
		}
		Definition::Local { owner, local } => {
			let body = sema.owner_body(owner)?;
			let parameter = matches!(owner, BodyOwner::Function(_))
				&& body.params().contains(&Some(local));
			let mutable = match body.local(local).mut_span {
				Some(_) => MODIFICATION,
				None => 0,
			};
			match parameter {
				true => (TokenType::Parameter, mutable),
				false => (TokenType::Variable, mutable),
			}
		}
		Definition::Field { owner, field } => {
			let fields = owner.fields(decls);
			let mutable = match decls.fields.mut_span(fields, field) {
				Some(_) => MODIFICATION,
				None => 0,
			};
			(TokenType::Property, mutable)
		}
		Definition::Parameter { .. } => (TokenType::Parameter, 0),
		Definition::TypeParam { .. } => (TokenType::TypeParameter, 0),
		// Only `Self` names an impl's target, and it is a keyword.
		Definition::InherentImplTarget(_) | Definition::TraitImplTarget(_) => {
			(TokenType::Keyword, 0)
		}
		Definition::Label { .. } => return None,
		Definition::JumpTarget { .. } => {
			unreachable!("a jump target is written as its keyword")
		}
		Definition::FunctionBody(_) => {
			unreachable!("a function's body is written as its `func` keyword")
		}
	};
	Some((kind, modifiers | default_library))
}

/// A function with a `self` receiver is a method; any other is a function.
fn function(snapshot: &Snapshot, index: FunctionIdx) -> TokenType {
	let function = &snapshot.sema.decls.functions[usize::from(index)];
	match snapshot.sema.decls.params.names(function.params).first() {
		Some(&Some(name)) if name == Keyword::SelfLower.symbol() => {
			TokenType::Method
		}
		_ => TokenType::Function,
	}
}
