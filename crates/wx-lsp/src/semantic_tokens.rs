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

use std::collections::BTreeMap;

use tower_lsp_server::ls_types::{
	Range, SemanticToken, SemanticTokenModifier, SemanticTokenType,
	SemanticTokensLegend,
};
use wx_compiler::diagnostics::TextSpan;
use wx_compiler::symbols::Keyword;
use wx_compiler::tir::{
	AccessKind, BodyOwner, DeclKind, Definition, FunctionIdx, MemberKind,
	Reference,
};
use wx_compiler::vfs::FileId;

use crate::convert::{
	byte_offset_to_utf16_offset, byte_to_position, position_to_offset,
};
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
/// A local or a field written to: assigned, or the target of `+=`.
const MODIFICATION: u32 = 1 << 3;
/// Provided by the compiler rather than defined in wx: an intrinsic (a
/// function std leaves to the compiler), a primitive type or a literal kind
/// (`Semantics::is_compiler_provided`). A std function with a body is an
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
			.get(span.start as usize..span.end as usize)
			.unwrap_or("")
	};

	// Each name's token, or `None` for a name that is not coloured. A
	// declaration is inserted after the uses, so it wins at a shared name,
	// even when it is not coloured itself.
	let mut tokens: BTreeMap<TextSpan, Option<(TokenType, u32)>> =
		BTreeMap::new();
	for (span, reference) in snapshot.sema.resolutions_in(file) {
		let span = span.span;
		if !wanted(span) {
			continue;
		}
		let modification = match reference {
			Reference::Local {
				access: AccessKind::Write | AccessKind::ReadWrite,
				..
			}
			| Reference::Field {
				access: AccessKind::Write | AccessKind::ReadWrite,
				..
			} => MODIFICATION,
			_ => 0,
		};
		let token = token(
			snapshot,
			reference.definition(),
			written(span),
			modification,
		);
		tokens.insert(span, token);
	}
	for (span, definition) in snapshot.definitions_in(file) {
		let span = span.span;
		if !wanted(span) {
			continue;
		}
		let token = token(snapshot, definition, written(span), DECLARATION);
		tokens.insert(span, token);
	}

	let mut data = Vec::new();
	let (mut line, mut character) = (0, 0);
	for (span, token) in tokens {
		let Some((kind, modifiers)) = token else {
			continue;
		};
		let position = byte_to_position(files, file, span.start as usize)?;
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
/// fits.
fn classify(
	snapshot: &Snapshot,
	definition: Definition,
) -> Option<(TokenType, u32)> {
	let sema = &snapshot.sema;
	let decls = &sema.decls;
	let default_library = match sema.is_compiler_provided(definition) {
		true => DEFAULT_LIBRARY,
		false => 0,
	};
	let (kind, modifiers) = match definition {
		Definition::Item(key) => match sema.declaration_kind(key) {
			DeclKind::Module(_)
			| DeclKind::Import(_)
			| DeclKind::Package(_)
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
			match parameter {
				true => (TokenType::Parameter, 0),
				false => (TokenType::Variable, 0),
			}
		}
		Definition::Field { .. } => (TokenType::Property, 0),
		Definition::Parameter { .. } => (TokenType::Parameter, 0),
		Definition::TypeParam { .. } => (TokenType::TypeParameter, 0),
		// Only `Self` names an impl's target, and it is a keyword.
		Definition::InherentImplTarget(_) | Definition::TraitImplTarget(_) => {
			(TokenType::Keyword, 0)
		}
		Definition::Label { .. } => return None,
	};
	Some((kind, modifiers | default_library))
}

/// A function with a `self` receiver is a method; any other is a function.
fn function(snapshot: &Snapshot, index: FunctionIdx) -> TokenType {
	let function = &snapshot.sema.decls.functions[usize::from(index)];
	match function.params.first() {
		Some(Some(name)) if name.inner == Keyword::SelfLower.symbol() => {
			TokenType::Method
		}
		_ => TokenType::Function,
	}
}
