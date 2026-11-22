//! Completion: what may be written at the cursor, read from the module's
//! syntax, and the names that fit there, from the checker
//! (`notes/lsp-completion-plan.md`).
//!
//! The syntax only says what kind of position the cursor is in, and which
//! declaration it is in, by the span of it the checker keeps; every
//! candidate comes from the checker's own lookups (`Semantics::names_at`,
//! `names_in_signature`, `names_in`, `names_in_scope`, `member_names`,
//! `type_member_names`,
//! `Body::labels_at`), so
//! nothing is offered that the checker would not accept written there.
//!
//! Each kind of site has its own provider: a name that means something
//! there (`references`), a name a declaration lists, to be filled in
//! (`slots`), a pattern (`patterns`), and a package instance's key. What
//! every candidate shares is `candidate`.

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{
	CompletionItem, CompletionItemKind, CompletionItemLabelDetails,
	CompletionParams, CompletionResponse, CompletionTextEdit, Documentation,
	MarkupContent, MarkupKind, TextEdit,
};
use wx_compiler::ast::{
	AST, AssocBinding, AssocBindingKind, Block, BlockId, BoundExpression,
	BoundId, Branch, Comment, CommentMap, ConstArgument, ConstId, Destructure,
	EnumVariant, ExprId, Expression, FunctionTypeParam, ImplItem,
	ImportDeclaration, ImportEntry, InColumn, Item, List, NamedArgument, PatId,
	Path, PathSegment, Pattern, PatternElement, PatternFieldItem,
	QualifiedPathRoot, SignatureId, Spanned, Statement, TraitItem,
	TypeArgument, TypeExpression, TypeId, TypeParam, UseTree, rest_span,
};
use wx_compiler::diagnostics::{SourceSpan, TextOffset, TextSpan};
use wx_compiler::tir::{
	DeclKind, Definition, MemberKind, NameUse, Scope, Tier, TraitIdx, TypeIndex,
};
use wx_compiler::vfs::FileId;

use crate::convert::{position_to_offset, span_to_range};
use crate::hover;
use crate::snapshot::Snapshot;
use crate::state::CompletionSupport;
use crate::state::ServerState;

mod patterns;
mod references;
mod slots;

use patterns::{PatternForms, PatternSite, PatternTarget};

/// The names that can be written at the cursor, in a body or a signature.
pub(crate) fn completion(
	state: &mut ServerState,
	params: &CompletionParams,
) -> Option<CompletionResponse> {
	let position = &params.text_document_position;
	let options = state.client.completion;
	let (snapshot, file) =
		state.resolve_uri_mut(&position.text_document.uri)?;
	let offset = position_to_offset(
		&snapshot.compilation.files,
		file,
		position.position,
	)?;
	let Position { site, within } = position_at(
		snapshot.compilation.ast(file),
		snapshot.compilation.comments(file),
		offset,
	)?;
	let items = match site {
		Site::PackageKey { literal } => {
			return package_keys(snapshot, file, literal, offset);
		}
		Site::Reference(site) => references::complete(
			&mut Request::new(snapshot, file, offset, within, options)?,
			site,
		)?,
		Site::Slot(site) => slots::complete(
			&mut Request::new(snapshot, file, offset, within, options)?,
			site,
		)?,
		Site::Pattern(site) => patterns::complete(
			&mut Request::new(snapshot, file, offset, within, options)?,
			site,
		)?,
	};
	Some(CompletionResponse::Array(items))
}

/// A completion at the cursor: the checked snapshot, where in it the cursor
/// is, and what the client takes.
struct Request<'a> {
	snapshot: &'a mut Snapshot,
	file: FileId,
	offset: TextOffset,
	within: Within,
	/// The declaration the cursor is in; `None` in a `use`.
	declaration: Option<Definition>,
	/// The scope the `use` the cursor is in is written in; `None` elsewhere.
	use_scope: Option<Scope>,
	/// What the client takes in the items.
	options: CompletionSupport,
}

impl<'a> Request<'a> {
	/// The request at `offset`, `within` a declaration or a `use`: `None`
	/// when the checker kept nothing for the one it is in.
	fn new(
		snapshot: &'a mut Snapshot,
		file: FileId,
		offset: TextOffset,
		within: Within,
		options: CompletionSupport,
	) -> Option<Self> {
		let declaration = match within {
			Within::Signature(Anchor::Name(name)) | Within::Body(name) => {
				Some(snapshot.declared_at(SourceSpan::new(file, name))?)
			}
			Within::Signature(Anchor::ImplTarget(target)) => {
				Some(snapshot.impl_with_target(SourceSpan::new(file, target))?)
			}
			Within::Use(_) => None,
		};
		// Where a `use` is written: the file, or the module or import block
		// named at a span.
		let use_scope = match within {
			Within::Use(Enclosing::File) => {
				Some(snapshot.sema.decls.file_namespaces[file.as_usize()])
			}
			Within::Use(Enclosing::Name(name)) => {
				let Definition::Item(loc) =
					snapshot.declared_at(SourceSpan::new(file, name))?
				else {
					return None;
				};
				Some(snapshot.sema.scope_entered_by(loc)?)
			}
			_ => None,
		};
		Some(Request {
			snapshot,
			file,
			offset,
			within,
			declaration,
			use_scope,
			options,
		})
	}
}

/// Where a candidate sorts among the others offered with it.
#[derive(Clone, Copy)]
enum Order {
	/// Locals and type parameters before items, as the lookup tries them
	/// first; each by name.
	ByName,
	/// At its position in the order its declaration lists it in.
	Listed(usize),
}

/// `item`, a name of a value of type `ty` here: shown as `name: Type` and,
/// with `label_details`, the type beside the name.
fn with_type(
	snapshot: &Snapshot,
	item: &mut CompletionItem,
	ty: TypeIndex,
	label_details: bool,
) {
	let shown = display_type(snapshot, ty);
	item.detail = Some(format!("{}: {shown}", item.label));
	type_beside(snapshot, item, ty, label_details);
}

/// With `label_details`, `ty` beside `item`'s name, its detail kept.
fn type_beside(
	snapshot: &Snapshot,
	item: &mut CompletionItem,
	ty: TypeIndex,
	label_details: bool,
) {
	if label_details {
		item.label_details = Some(CompletionItemLabelDetails {
			detail: None,
			description: Some(display_type(snapshot, ty)),
		});
	}
}

fn display_type(snapshot: &Snapshot, ty: TypeIndex) -> String {
	snapshot
		.sema
		.type_formatter(&snapshot.strings)
		.display_type(ty)
}

/// What every candidate has, whatever its site: its name, kind, signature
/// and documentation, sorted by `order`.
fn candidate(
	snapshot: &Snapshot,
	name: SymbolU32,
	definition: Definition,
	order: Order,
) -> CompletionItem {
	let label = snapshot
		.strings
		.resolve(name)
		.unwrap_or_default()
		.to_string();
	let (kind, rank) = match definition {
		Definition::Local { .. } => (CompletionItemKind::VARIABLE, 0),
		Definition::TypeParam { .. } => (CompletionItemKind::TYPE_PARAMETER, 0),
		Definition::InherentImplTarget(_) | Definition::TraitImplTarget(_) => {
			(CompletionItemKind::STRUCT, 0)
		}
		Definition::Label { .. } => (CompletionItemKind::REFERENCE, 0),
		Definition::JumpTarget { .. } | Definition::FunctionBody(_) => {
			unreachable!("a jump's destination has no name to complete")
		}
		Definition::Parameter { .. } => (CompletionItemKind::VARIABLE, 0),
		Definition::Field { .. } => (CompletionItemKind::FIELD, 0),
		Definition::Member(MemberKind::Method(_)) => {
			(CompletionItemKind::METHOD, 0)
		}
		Definition::Member(MemberKind::Function(_)) => {
			(CompletionItemKind::FUNCTION, 0)
		}
		Definition::Member(MemberKind::AssociatedType(_)) => {
			(CompletionItemKind::STRUCT, 0)
		}
		Definition::Member(MemberKind::Constant(_)) => {
			(CompletionItemKind::CONSTANT, 0)
		}
		Definition::Item(loc) => {
			let kind = match snapshot.sema.declaration_kind(loc) {
				DeclKind::Module(_)
				| DeclKind::Import(_)
				| DeclKind::Package(_)
				| DeclKind::PackageInstance(_) => CompletionItemKind::MODULE,
				DeclKind::Enum(_) => CompletionItemKind::ENUM,
				DeclKind::EnumVariant(_) => CompletionItemKind::ENUM_MEMBER,
				DeclKind::Struct(_)
				| DeclKind::Memory(_)
				| DeclKind::AssocType(_)
				| DeclKind::TypeAlias(_) => CompletionItemKind::STRUCT,
				DeclKind::Trait(_) | DeclKind::TypeSet(_) => {
					CompletionItemKind::INTERFACE
				}
				DeclKind::Global(_) => CompletionItemKind::VARIABLE,
				DeclKind::Function(_) => CompletionItemKind::FUNCTION,
				DeclKind::Const(_) => CompletionItemKind::CONSTANT,
			};
			(kind, 1)
		}
	};
	CompletionItem {
		sort_text: Some(match order {
			Order::ByName => format!("{rank}{label}"),
			Order::Listed(at) => format!("{at:04}"),
		}),
		detail: hover::signature(&snapshot.sema, &snapshot.strings, definition),
		documentation: hover::documentation(
			&snapshot.sema,
			&snapshot.compilation.files,
			definition,
		)
		.map(|value| {
			Documentation::MarkupContent(MarkupContent {
				kind: MarkupKind::Markdown,
				value,
			})
		}),
		kind: Some(kind),
		label,
		..Default::default()
	}
}

/// The keys the manifest of `file`'s package declares its dependencies
/// under, for the literal of a package instance written at `literal`, the
/// cursor at `offset` in it. Each replaces what is written between the
/// quotes, and closes a literal left open. The core, bound in every package
/// already, is not offered.
fn package_keys(
	snapshot: &Snapshot,
	file: FileId,
	literal: TextSpan,
	offset: TextOffset,
) -> Option<CompletionResponse> {
	let compilation = &snapshot.compilation;
	let source = &compilation.files.get(file).ok()?.source;
	// Read as the lexer reads it: an escape skips the character after it,
	// and an unescaped quote closes the literal.
	let mut contents = source
		[usize::from(literal.start) + 1..usize::from(literal.end)]
		.chars();
	let mut closed = false;
	while let Some(c) = contents.next() {
		match c {
			'\\' => _ = contents.next(),
			'"' => closed = true,
			_ => {}
		}
	}
	// After the closing quote is past the literal.
	if closed && offset == literal.end {
		return None;
	}
	// An open literal runs to the end of the file, so only what is typed
	// before the cursor is replaced.
	let end = if closed { literal.end - 1 } else { offset };
	let range = span_to_range(
		&compilation.files,
		SourceSpan::new(file, TextSpan::new(literal.start + 1, end)),
	)?;
	let package = compilation.package_of(file)?;
	let mut keys: Vec<_> = (package.dependencies.iter())
		.filter(|&(_, &dependency)| dependency != compilation.core_package)
		.filter_map(|(&key, &dependency)| {
			Some((snapshot.strings.resolve(key)?, dependency))
		})
		.collect();
	keys.sort_unstable_by_key(|&(key, _)| key);
	let items = keys
		.into_iter()
		.map(|(key, dependency)| {
			let mut new_text = key.replace('\\', "\\\\").replace('"', "\\\"");
			if !closed {
				new_text.push('"');
			}
			let root = compilation.packages[dependency.as_usize()]
				.entry_path
				.parent();
			CompletionItem {
				label: key.to_owned(),
				kind: Some(CompletionItemKind::MODULE),
				detail: Some(root.as_str().to_owned()),
				filter_text: Some(key.to_owned()),
				text_edit: Some(CompletionTextEdit::Edit(TextEdit {
					range,
					new_text,
				})),

				..CompletionItem::default()
			}
		})
		.collect();
	Some(CompletionResponse::Array(items))
}

/// Where the cursor is: what can be written there, and in which part of
/// which declaration.
pub(crate) struct Position {
	site: Site,
	within: Within,
}

/// The part of a declaration the cursor is in: a signature, read in the
/// declaration's scope, or a body, which adds its locals and labels. Only a
/// named declaration has a body.
#[derive(Clone, Copy)]
pub(crate) enum Within {
	Signature(Anchor),
	/// The body of the declaration named at this span.
	Body(TextSpan),
	/// A `use` or a package instance, written directly in a scope rather
	/// than in a declaration.
	Use(Enclosing),
}

impl Within {
	/// The position of `site`, when the cursor is at one, in this part.
	fn position(self, site: Option<Site>) -> Option<Position> {
		Some(Position {
			site: site?,
			within: self,
		})
	}
}

/// A declaration, by the one span of it the checker keeps: an item's name
/// (a member's included), an impl's target path (`query::impls`).
#[derive(Clone, Copy)]
pub(crate) enum Anchor {
	Name(TextSpan),
	ImplTarget(TextSpan),
}

/// The scope a `use` is written in: the file's own, or the one a module or
/// an import block named at this span opens.
#[derive(Clone, Copy)]
pub(crate) enum Enclosing {
	File,
	Name(TextSpan),
}

/// What the entry of a bound's `where { .. }` block at the cursor can still
/// name.
#[derive(Clone, Copy)]
pub(crate) enum Entry {
	/// Not written yet, or a name with nothing after it: an associated type,
	/// or a constant, inserted with its `const`.
	Unmarked,
	/// An associated type's, its `=` or `:` written.
	Type,
	/// A constant's, marked `const`.
	Constant,
}

impl Entry {
	fn tiers(self) -> &'static [Tier] {
		match self {
			Self::Unmarked => &[Tier::Type, Tier::Value],
			Self::Type => &[Tier::Type],
			Self::Constant => &[Tier::Value],
		}
	}
}

/// What an item inserts: its name, or, for a function, method or constructor in
/// a value position, its call (when the client takes snippets).
#[derive(Clone, Copy)]
pub(crate) enum Insert {
	Name,
	Call,
}

/// A `break` or a `continue`.
#[derive(Clone, Copy)]
pub(crate) enum Jump {
	Break,
	Continue,
}

/// What can be written at the cursor, as completion offers it: one kind of
/// site per provider.
pub(crate) enum Site {
	/// A name that means something at the cursor (`references`).
	Reference(ReferenceSite),
	/// An ordinary match-pattern name or positional insertion, whose type
	/// comes from checked patterns or the prospective insertion layout.
	Pattern(PatternSite),
	/// A name a declaration lists, to be filled in.
	Slot(SlotSite),
	/// The manifest key of a package instance, in its string literal
	/// written at `literal`, opening quote included.
	PackageKey { literal: TextSpan },
}

/// A name that means something at the cursor (`references::complete`).
pub(crate) enum ReferenceSite {
	/// A bare name, used as its `NameUse` says.
	Name(NameUse),
	/// A path's segment after another, used as `used_as` in what the one
	/// before it, written at `prefix`, means.
	Segment { prefix: TextSpan, used_as: NameUse },
	/// A member of the object as the body checked it.
	Member { object: ExprId },
	/// The segment after a trait-qualified root, `<T as Tr>::`, used as
	/// `used_as`: one of the members of the trait whose last name is
	/// written at `trait_name`.
	TraitMember {
		trait_name: TextSpan,
		used_as: NameUse,
	},
	/// The label of a jump.
	Label(Jump),
	/// The last segment of a `use` path, after the one written at `prefix`,
	/// in a group that lists `written` already.
	Import {
		prefix: TextSpan,
		written: Vec<SymbolU32>,
	},
}

/// A name a declaration lists, to be filled in at the cursor
/// (`slots::complete`).
pub(crate) enum SlotSite {
	/// The name of an entry of a bound's `where { .. }` block, the `entry`
	/// at the cursor: a member of the trait whose name is written at `bound`,
	/// not among the `written` ones (by tier).
	Binding {
		bound: TextSpan,
		entry: Entry,
		written: Vec<(Tier, SymbolU32)>,
	},
	/// The name of a field in the struct pattern `pattern`, with braces: one
	/// of the fields of the struct or enum whose last name is written at
	/// `owner`, not among the `written` ones.
	PatternField {
		pattern: PatId,
		owner: TextSpan,
		written: Vec<SymbolU32>,
	},
	/// The name of an argument in a named list: one of the parameters of
	/// `target`, not among the `written` ones.
	Argument {
		target: ArgumentTarget,
		written: Vec<SymbolU32>,
	},
}

/// What has the parameters a named list's names name.
pub(crate) enum ArgumentTarget {
	/// The callee whose last name is written at `callee`, in `call`, after
	/// the first `given` (a method call's receiver).
	Call {
		call: ExprId,
		callee: TextSpan,
		given: usize,
	},
	/// The loop the `continue` written as `jump` restarts, as it was
	/// checked.
	Loop { jump: ExprId },
}

/// The source following the identifier at the cursor, ignoring whitespace
/// and the comments already identified by the parser.
fn after_name<'a>(
	source: &'a str,
	comments: &CommentMap,
	offset: TextOffset,
) -> &'a str {
	let suffix = source[usize::from(offset)..]
		.trim_start_matches(|c: char| c.is_alphanumeric() || c == '_');
	let start = TextOffset::from((source.len() - suffix.len()) as u32);
	let mut suffix = suffix.trim_start();
	for comment in
		comments.between(start, TextOffset::from(source.len() as u32))
	{
		if usize::from(comment.span.start) != source.len() - suffix.len() {
			break;
		}
		suffix = source[usize::from(comment.span.end)..].trim_start();
	}
	suffix
}

/// The secondary label of a member a trait supplies: `(as Trait)`.
fn as_trait(snapshot: &Snapshot, index: TraitIdx) -> Option<String> {
	let decls = &snapshot.sema.decls;
	let name = decls.item(decls.traits[usize::from(index)].loc).name.inner;
	Some(format!("(as {})", snapshot.strings.resolve(name)?))
}

/// What can be written at `offset`, and where: a name being written (its
/// own span reaches the cursor), a member after an object, or a value or
/// type not written yet (an error node the parser kept, or the room between
/// a block's statements or a list's elements), in a declaration's signature
/// or body. `None`
/// anywhere else: in a comment, a declaration's own name, a literal, a
/// segment after a type, a `use` path's alias or `*`, or an `export`.
///
/// One path down the module's syntax: at each level the child at the
/// cursor is found by a binary search of its siblings, which are in source
/// order and do not overlap.
pub(crate) fn position_at(
	ast: &AST,
	comments: &CommentMap,
	offset: TextOffset,
) -> Option<Position> {
	let cursor = Cursor { offset, ast };
	// Inside a comment: its start is the `//` itself, its end the line's.
	let comment = cursor.child(&comments.0);
	if comment.is_some_and(|comment| comment.span.start < offset) {
		return None;
	}
	cursor.item(&cursor.node(ast.root)?, Enclosing::File)
}

/// A piece of syntax the walker searches by where it is written.
trait Node {
	fn span(&self) -> TextSpan;
}

impl<T> Node for Spanned<T> {
	fn span(&self) -> TextSpan {
		self.span
	}
}

impl Node for Path {
	fn span(&self) -> TextSpan {
		self.span
	}
}

impl Node for AssocBinding {
	fn span(&self) -> TextSpan {
		self.span
	}
}

impl Node for FunctionTypeParam {
	fn span(&self) -> TextSpan {
		self.span
	}
}

impl Node for Comment {
	fn span(&self) -> TextSpan {
		self.span
	}
}

struct Cursor<'a> {
	offset: TextOffset,
	/// The file's tree, where its type syntax is read by id.
	ast: &'a AST,
}

impl Cursor<'_> {
	/// Whether the cursor touches `span`: inside it, or at either end, where
	/// a name being typed ends.
	fn at(&self, span: TextSpan) -> bool {
		span.start <= self.offset && self.offset <= span.end
	}

	/// Whether the cursor is between the delimiters that start and end
	/// `span`, where something not written yet can go.
	fn inside(&self, span: TextSpan) -> bool {
		span.start < self.offset && self.offset < span.end
	}

	/// The one of `siblings` (in source order, not overlapping, as written)
	/// the cursor touches. When two do, one ending where the next starts,
	/// the first: the name being typed ends at the cursor.
	fn child<'a, T: Node>(&self, siblings: &'a [T]) -> Option<&'a T> {
		Some(&siblings[self.child_index(siblings)?])
	}

	/// The node of `list` the cursor touches, as `child` finds it among the
	/// spans its column keeps beside it.
	fn node<T: InColumn + Copy>(&self, list: List<T>) -> Option<T> {
		let index = self.child_index_by(self.ast.spans(list), |span| *span)?;
		Some(self.ast.list(list)[index])
	}

	/// `child`, for siblings whose spans are read through the tree (`span`):
	/// the ids of types, bounds and type arguments.
	fn child_by<'s, T>(
		&self,
		siblings: &'s [T],
		span: impl Fn(&T) -> TextSpan,
	) -> Option<&'s T> {
		Some(&siblings[self.child_index_by(siblings, span)?])
	}

	/// Where in `siblings` the one `child_by` finds is.
	fn child_index_by<T>(
		&self,
		siblings: &[T],
		span: impl Fn(&T) -> TextSpan,
	) -> Option<usize> {
		let index =
			siblings.partition_point(|sibling| span(sibling).end < self.offset);
		self.at(span(siblings.get(index)?)).then_some(index)
	}

	/// Where in `siblings` the one `child` finds is.
	fn child_index<T: Node>(&self, siblings: &[T]) -> Option<usize> {
		let index = siblings
			.partition_point(|sibling| sibling.span().end < self.offset);
		self.at(siblings.get(index)?.span()).then_some(index)
	}

	/// An item written in the scope `scope`.
	fn item(&self, item: &Item, scope: Enclosing) -> Option<Position> {
		match item {
			Item::Function {
				signature, block, ..
			} => self.function(*signature, Some(*block)),
			Item::FunctionDeclaration { signature, .. }
			| Item::PackageFunction { signature, .. } => self.function(*signature, None),
			Item::PackageConst { name, ty, .. }
			| Item::Memory { name, size: ty, .. } => {
				Within::Signature(Anchor::Name(name.span))
					.position(self.ty(*ty))
			}
			Item::PackageType {
				name, type_params, ..
			} => Within::Signature(Anchor::Name(name.span))
				.position(self.type_params(*type_params)),
			Item::Global {
				name, ty, value, ..
			}
			| Item::Const {
				name, ty, value, ..
			} => self.constant(name.span, *ty, Some(*value)),
			Item::Enum {
				name,
				repr,
				variants,
				..
			} => Within::Signature(Anchor::Name(name.span))
				.position(self.node(*repr).and_then(|field| self.ty(field.ty?)))
				.or_else(|| {
					let variant: EnumVariant = self.node(*variants)?;
					Within::Body(variant.name.span)
						.position(self.expression(variant.value?))
				}),
			Item::Struct {
				name,
				type_params,
				fields,
				..
			} => Within::Signature(Anchor::Name(name.span)).position(
				self.type_params(*type_params)
					.or_else(|| self.ty(self.node(*fields)?.ty?)),
			),
			Item::TypeAlias {
				name,
				type_params,
				body,
				..
			} => Within::Signature(Anchor::Name(name.span)).position(
				self.type_params(*type_params).or_else(|| self.ty((*body)?)),
			),
			Item::TypeSet {
				name,
				bounds,
				members,
				..
			} => Within::Signature(Anchor::Name(name.span)).position(
				bounds
					.as_ref()
					.and_then(|bounds| self.bound(*bounds))
					.or_else(|| {
						let member = self.child(self.ast.list(*members))?;
						self.path(self.ast.list(member.segments), NameUse::Type)
					}),
			),
			Item::Trait {
				name,
				supertraits,
				items,
				..
			} => {
				let header = Within::Signature(Anchor::Name(name.span));
				header
					.position(
						supertraits
							.as_ref()
							.and_then(|bounds| self.bound(*bounds)),
					)
					.or_else(|| match &self.node(*items)? {
						TraitItem::Function {
							signature, body, ..
						} => self.function(*signature, *body),
						TraitItem::Const {
							name, ty, value, ..
						} => self.constant(name.span, Some(*ty), *value),
						// Read in the trait's scope, where `Self` is the
						// trait's.
						TraitItem::AssociatedType { bounds, value, .. } => {
							header.position(
								bounds
									.as_ref()
									.and_then(|bounds| self.bound(*bounds))
									.or_else(|| self.ty(*value.as_ref()?)),
							)
						}
					})
			}
			Item::InherentImpl {
				type_params,
				target,
				items,
				..
			} => self.impl_block(*type_params, None, target, *items),
			Item::TraitImpl {
				type_params,
				trait_name,
				target,
				items,
				..
			} => self.impl_block(*type_params, Some(trait_name), target, *items),
			Item::Import {
				entries,
				internal_name,
				..
			} => {
				let entry = self.node(*entries)?;
				let declaration = match &entry {
					ImportEntry::Declaration { declaration, .. } => declaration,
					ImportEntry::Use { tree, .. } => {
						return self.use_tree(
							self.ast.use_tree(*tree),
							None,
							Enclosing::Name(internal_name.span),
						);
					}
				};
				match declaration {
					ImportDeclaration::Function { signature } => {
						self.function(*signature, None)
					}
					ImportDeclaration::Global { name, ty, .. }
					| ImportDeclaration::Memory { name, size: ty } => {
						Within::Signature(Anchor::Name(name.span))
							.position(self.ty(*ty))
					}
				}
			}
			Item::Module { name, items, .. } => {
				self.item(&self.node(*items)?, Enclosing::Name(name.span))
			}
			Item::Use { tree, .. } => {
				self.use_tree(self.ast.use_tree(*tree), None, scope)
			}
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::ModuleDeclaration { .. } => None,
			// Between the quotes, or after the opening one of a literal not
			// closed yet.
			Item::PackageInstance { package, .. } => {
				(package.start < self.offset && self.offset <= package.end)
					.then_some(())?;
				Within::Use(scope)
					.position(Some(Site::PackageKey { literal: *package }))
			}
		}
	}

	/// A `use` tree written in `scope`, after the segment written at
	/// `prefix`, as import resolution reads it: the first segment is looked
	/// up in the scope, one with more after it is a namespace, and the last
	/// after a prefix (a leaf) is anything. Inside a group's braces, a gap
	/// between branches is a leaf not written yet. An alias and a `*` are
	/// nothing to complete.
	fn use_tree(
		&self,
		tree: UseTree,
		prefix: Option<TextSpan>,
		scope: Enclosing,
	) -> Option<Position> {
		// A segment with more after it, or the first one.
		let continued = |segment: Spanned<_>| {
			self.at(segment.span).then_some(match prefix {
				None => {
					Site::Reference(ReferenceSite::Name(NameUse::Namespace))
				}
				Some(prefix) => Site::Reference(ReferenceSite::Segment {
					prefix,
					used_as: NameUse::Namespace,
				}),
			})
		};
		let site = match tree {
			UseTree::Name { segment, .. } => match prefix {
				None => continued(segment),
				Some(prefix) => self.at(segment.span).then(|| {
					Site::Reference(ReferenceSite::Import {
						prefix,
						written: Vec::new(),
					})
				}),
			},
			UseTree::Glob { segment } => continued(segment),
			UseTree::Path { segment, rest } => {
				if continued(segment).is_none() {
					let rest = self.ast.use_tree(rest);
					return self.use_tree(rest, Some(segment.span), scope);
				}
				continued(segment)
			}
			UseTree::Group {
				segment,
				branches,
				braces,
			} => {
				if continued(segment).is_some() || !self.inside(braces) {
					continued(segment)
				} else {
					let trees = self.ast.list(branches);
					let at = self
						.child_index_by(self.ast.spans(branches), |span| *span);
					match at.map(|index| trees[index]) {
						// Its alias.
						Some(UseTree::Name { segment: name, .. })
							if !self.at(name.span) =>
						{
							None
						}
						Some(
							branch @ (UseTree::Path { .. }
							| UseTree::Glob { .. }
							| UseTree::Group { .. }),
						) => {
							return self.use_tree(
								branch,
								Some(segment.span),
								scope,
							);
						}
						// A leaf being written, or one not written yet.
						_ => Some(Site::Reference(ReferenceSite::Import {
							prefix: segment.span,
							written: (trees.iter().enumerate())
								.filter(|&(index, _)| Some(index) != at)
								.filter_map(|(_, tree)| match tree {
									UseTree::Name { segment, .. } => {
										Some(segment.inner)
									}
									_ => None,
								})
								.collect(),
						})),
					}
				}
			}
		};
		Within::Use(scope).position(site)
	}

	/// A function, by its name: its signature, then its body if it has one.
	fn function(
		&self,
		signature: SignatureId,
		body: Option<BlockId>,
	) -> Option<Position> {
		let signature = self.ast.signature(signature);
		let name = signature.name.span;
		let site = self
			.type_params(signature.type_params)
			.or_else(|| self.ty(self.node(signature.params)?.ty?))
			.or_else(|| self.ty(signature.result?));
		Within::Signature(Anchor::Name(name))
			.position(site)
			.or_else(|| Within::Body(name).position(self.block(body?)))
	}

	/// A constant or a global, by its name: its type, then its value.
	fn constant(
		&self,
		name: TextSpan,
		ty: Option<TypeId>,
		value: Option<ExprId>,
	) -> Option<Position> {
		Within::Signature(Anchor::Name(name))
			.position(ty.and_then(|ty| self.ty(ty)))
			.or_else(|| Within::Body(name).position(self.expression(value?)))
	}

	/// An impl: its header, read in its own scope, and its members.
	fn impl_block(
		&self,
		type_params: List<TypeParam>,
		trait_name: Option<&Path>,
		target: &Path,
		items: List<ImplItem>,
	) -> Option<Position> {
		let header = Within::Signature(Anchor::ImplTarget(target.span));
		let site = self
			.type_params(type_params)
			.or_else(|| {
				self.path(self.ast.list(trait_name?.segments), NameUse::Trait)
			})
			.or_else(|| {
				self.path(self.ast.list(target.segments), NameUse::Type)
			});
		header.position(site).or_else(|| {
			match &self.node(items)? {
				ImplItem::Function {
					signature, block, ..
				} => self.function(*signature, Some(*block)),
				ImplItem::Constant {
					name, ty, value, ..
				} => self.constant(name.span, *ty, Some(*value)),
				// Read in the impl's scope.
				ImplItem::AssocType { ty, .. } => header.position(self.ty(*ty)),
			}
		})
	}

	fn type_params(&self, params: List<TypeParam>) -> Option<Site> {
		match self.node(params)? {
			TypeParam::Type { bounds, .. } => self.bound(bounds?),
			TypeParam::Const { ty, .. } => self.ty(ty),
		}
	}

	/// A bound names a trait or a typeset; a binding's own name (`Size` in
	/// `where { Size = u32 }`) is a member of the trait.
	fn bound(&self, bound: BoundId) -> Option<Site> {
		let ast = self.ast;
		let span = ast.bound_span(bound);
		if !self.at(span) {
			return None;
		}
		match ast.bound(bound) {
			// A bound the parser expected and did not find.
			BoundExpression::Error => {
				Some(Site::Reference(ReferenceSite::Name(NameUse::Bound)))
			}
			BoundExpression::Path(segments) => {
				self.path(ast.list(segments), NameUse::Bound)
			}
			BoundExpression::WithBindings {
				path,
				bindings,
				open_brace,
			} => self.path(ast.list(path), NameUse::Bound).or_else(|| {
				self.bindings(
					ast.list(path).last()?.ident.span,
					ast.list(bindings),
					TextSpan::new(open_brace, span.end),
				)
			}),
			BoundExpression::BoundList(bounds) => self.bound(
				*self.child_by(ast.list(bounds), |&b| ast.bound_span(b))?,
			),
		}
	}

	/// A bound's `where { .. }` entries, in their braces: the name of the
	/// one at the cursor, or one not written yet in the room between two, is
	/// a member of the trait named at `bound` that the entry can still name
	/// (`Entry`), minus the names written already; after its `=` or `:` is
	/// a type or a bound.
	fn bindings(
		&self,
		bound: TextSpan,
		bindings: &[AssocBinding],
		braces: TextSpan,
	) -> Option<Site> {
		if !self.inside(braces) {
			return None;
		}
		let at = self.child_index_by(bindings, |binding| binding.span);
		let mut entry = Entry::Unmarked;
		if let Some(at) = at {
			let binding = &bindings[at];
			if !self.at(binding.name.span) {
				return match binding.kind {
					AssocBindingKind::Equals(ty)
					| AssocBindingKind::ConstRepresentable { ty, .. } => self.ty(ty),
					AssocBindingKind::Bound(bound) => self.bound(bound),
					AssocBindingKind::ConstEquals { value, .. } => {
						self.const_argument(value)
					}
				};
			}
			entry = self.entry(binding);
		}
		Some(Site::Slot(SlotSite::Binding {
			bound,
			entry,
			written: (bindings.iter().enumerate())
				.filter(|&(index, _)| Some(index) != at)
				.map(|(_, binding)| {
					let tier = match self.entry(binding) {
						Entry::Constant => Tier::Value,
						Entry::Unmarked | Entry::Type => Tier::Type,
					};
					(tier, binding.name.inner)
				})
				.collect(),
		}))
	}

	/// What an entry of a `where` block is, by what is written around its
	/// name. A name with nothing after it is kept with an error type that
	/// starts right at its end, where its `=` would be (`{ Si }`).
	fn entry(&self, binding: &AssocBinding) -> Entry {
		match binding.kind {
			AssocBindingKind::ConstRepresentable { .. }
			| AssocBindingKind::ConstEquals { .. } => Entry::Constant,
			AssocBindingKind::Equals(ty)
				if matches!(self.ast.ty(ty), TypeExpression::Error)
					&& self.ast.type_span(ty).start
						== binding.name.span.end =>
			{
				Entry::Unmarked
			}
			AssocBindingKind::Equals(_) | AssocBindingKind::Bound(_) => {
				Entry::Type
			}
		}
	}

	fn statement(&self, statement: Statement) -> Option<Site> {
		match statement {
			Statement::Expression(expression) => self.expression(expression),
			Statement::LocalDefinition { pattern, ty, value } => self
				.pattern(pattern, PatternForms::Bindings)
				.or_else(|| self.ty(ty?))
				.or_else(|| self.expression(value)),
		}
	}

	/// A block: the statement at the cursor, its tail, or between its
	/// braces, where a statement can start.
	fn block(&self, block: BlockId) -> Option<Site> {
		let ast = self.ast;
		let span = ast.block_span(block);
		if !self.at(span) {
			return None;
		}
		let Block { statements, tail } = ast.block(block);
		let statement =
			self.child_by(ast.list(statements), |&s| ast.statement_span(s));
		match (statement, tail) {
			(Some(&statement), _) => self.statement(ast.statement(statement)),
			(None, Some(tail)) if self.at(ast.expr_span(tail)) => {
				self.expression(tail)
			}
			_ => self.inside(span).then_some(Site::Reference(
				ReferenceSite::Name(NameUse::Value),
			)),
		}
	}

	/// An `else` branch or a match arm's body.
	fn branch(&self, branch: Branch) -> Option<Site> {
		match branch {
			Branch::Block(block) => self.block(block),
			Branch::Expression(expression) => self.expression(expression),
		}
	}

	fn expression(&self, expression: ExprId) -> Option<Site> {
		let ast = self.ast;
		let span = ast.expr_span(expression);
		if !self.at(span) {
			return None;
		}
		match ast.expr(expression) {
			// A value the parser expected and did not find.
			Expression::Error => {
				Some(Site::Reference(ReferenceSite::Name(NameUse::Value)))
			}
			Expression::Path(segments) => {
				self.path(ast.list(segments), NameUse::Value)
			}
			// Before the braces is the keyword and the label, where nothing
			// is looked up.
			Expression::Block { block, .. } => self.block(block),
			Expression::Unary { operand, .. } => self.expression(operand),
			Expression::Binary { left, right, .. } => {
				self.expression(left).or_else(|| self.expression(right))
			}
			Expression::Call { callee, arguments } => {
				let (named, braces) = match ast.expr(arguments) {
					Expression::NamedList { arguments: named } => {
						(named, ast.expr_span(arguments))
					}
					Expression::Tuple { elements } => {
						return self.expression(callee).or_else(|| {
							self.list(
								ast.arguments_span(arguments),
								ast.list(elements),
							)
						});
					}
					_ => {
						return self
							.expression(callee)
							.or_else(|| self.expression(arguments));
					}
				};
				// A method's object gives its receiver, one argument given.
				let (name, given) = match ast.expr(callee) {
					Expression::Path(segments)
					| Expression::QualifiedPath { segments, .. } => (
						ast.list(segments)
							.last()
							.map(|segment| segment.ident.span),
						0,
					),
					Expression::ObjectAccess { member, .. } => {
						(Some(ast.segment(member).ident.span), 1)
					}
					_ => (None, 0),
				};
				self.expression(callee).or_else(|| {
					let target = name.map(|callee| ArgumentTarget::Call {
						call: expression,
						callee,
						given,
					});
					self.named(target, ast.list(named), braces)
				})
			}
			// Outside a call's or a `continue`'s arguments its names mean
			// nothing; only the values are walked.
			Expression::NamedList { arguments, .. } => ast
				.list(arguments)
				.iter()
				.find_map(|argument| self.expression(argument.value?)),
			Expression::ObjectAccess { object, member } => self
				.expression(object)
				.or_else(|| self.type_args(&ast.segment(member)))
				.or_else(|| {
					(ast.expr_span(object).end < self.offset
						&& self.offset <= ast.segment(member).ident.span.end)
						.then_some(Site::Reference(ReferenceSite::Member {
							object,
						}))
				}),
			Expression::Deref { pointer: value }
			| Expression::AddressOf { value } => self.expression(value),
			Expression::Return { value } => self.expression(value?),
			Expression::Break { label, value } => self
				.label(label, Jump::Break)
				.or_else(|| self.expression(value?)),
			Expression::Continue { label, value } => {
				self.label(label, Jump::Continue).or_else(|| {
					let value = value?;
					match ast.expr(value) {
						// Its names are the parameters of the loop it was
						// checked to restart.
						Expression::NamedList { arguments } => self.named(
							Some(ArgumentTarget::Loop { jump: expression }),
							ast.list(arguments),
							ast.expr_span(value),
						),
						_ => self.expression(value),
					}
				})
			}
			Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self
				.expression(condition)
				.or_else(|| self.block(then_block))
				.or_else(|| self.branch(else_block?)),
			Expression::Match {
				scrutinee,
				arms,
				open_brace,
			} => self.expression(scrutinee).or_else(|| {
				let arm = self.child_by(ast.list(arms), |arm| {
					TextSpan::new(
						ast.pattern_span(arm.pattern).start,
						ast.branch_span(arm.body).end,
					)
				});
				match arm {
					Some(arm) => self
						.pattern(arm.pattern, PatternForms::Tests)
						.or_else(|| self.branch(arm.body)),
					None => self
						.inside(TextSpan::new(open_brace, span.end))
						.then_some(Site::Pattern(PatternSite {
							target: PatternTarget::MatchGap(expression),
							prefix: None,
							forms: PatternForms::Tests,
							ancestors: Vec::new(),
						})),
				}
			}),
			Expression::Loop { header, block, .. } => header
				.and_then(|header| {
					let header = ast.loop_header(header);
					self.node(header.params)
						.and_then(|param| self.ty(param.ty?))
						.or_else(|| {
							let initials = ast.list(header.initials);
							let initial = self
								.child_by(initials, |&initial| {
									ast.expr_span(initial)
								})?;
							self.expression(*initial)
						})
				})
				.or_else(|| self.block(block)),
			Expression::QualifiedPath { root, segments } => self
				.qualified_path(
					ast.qualified_root(root),
					ast.list(segments),
					NameUse::Value,
				),
			Expression::Grouped { inner, .. } => self.ty(inner),
			Expression::Tuple { elements }
			| Expression::ArrayList { elements } => self.list(span, ast.list(elements)),
			Expression::Ascription { value, ty } => {
				self.expression(value).or_else(|| self.ty(ty))
			}
			Expression::ArrayRepeat { value, count } => self
				.expression(value)
				.or_else(|| self.const_argument(count)),
			Expression::Index { object, index } => {
				self.expression(object).or_else(|| self.expression(index))
			}
			Expression::Int { .. }
			| Expression::Float
			| Expression::Char
			| Expression::String
			| Expression::Placeholder => None,
		}
	}

	/// A list of values in the delimiters that start and end `delimiters`:
	/// the element at the cursor, or a value not written yet in the room
	/// between two (`f(a, |)`).
	fn list(&self, delimiters: TextSpan, elements: &[ExprId]) -> Option<Site> {
		match self.child_by(elements, |&element| self.ast.expr_span(element)) {
			Some(&element) => self.expression(element),
			None => self.inside(delimiters).then_some(Site::Reference(
				ReferenceSite::Name(NameUse::Value),
			)),
		}
	}

	/// A named list's arguments, in their braces: the name of the one at the
	/// cursor, or one not written yet in the room between two, is one of
	/// `target`'s parameters (none for a callee without a last name); after
	/// a name's `:` is its value. Outside the braces nothing is: a list not
	/// closed yet offers no names.
	fn named(
		&self,
		target: Option<ArgumentTarget>,
		arguments: &[NamedArgument],
		braces: TextSpan,
	) -> Option<Site> {
		if !self.inside(braces) {
			return None;
		}
		let ast = self.ast;
		let at = self.child_index_by(arguments, |argument| {
			let end = argument.value.map_or(argument.name.span.end, |value| {
				ast.expr_span(value).end
			});
			TextSpan::new(argument.name.span.start, end)
		});
		if let Some(at) = at {
			let argument = &arguments[at];
			if !self.at(argument.name.span) {
				return self.expression(argument.value?);
			}
		}
		let written = (arguments.iter().enumerate())
			.filter(|&(index, _)| Some(index) != at)
			.map(|(_, argument)| argument.name.inner)
			.collect();
		Some(Site::Slot(SlotSite::Argument {
			target: target?,
			written,
		}))
	}

	fn ty(&self, ty: TypeId) -> Option<Site> {
		let ast = self.ast;
		if !self.at(ast.type_span(ty)) {
			return None;
		}
		match ast.ty(ty) {
			// A type the parser expected and did not find.
			TypeExpression::Error => {
				Some(Site::Reference(ReferenceSite::Name(NameUse::Type)))
			}
			TypeExpression::Path(segments) => {
				self.path(ast.list(segments), NameUse::Type)
			}
			TypeExpression::Tuple { elements } => self
				.ty(*self
					.child_by(ast.list(elements), |&e| ast.type_span(e))?),
			TypeExpression::Function { params, result, .. } => self
				.child(ast.list(params))
				.and_then(|param| self.ty(param.ty))
				.or_else(|| self.ty(result?)),
			TypeExpression::Pointer { inner, .. }
			| TypeExpression::Slice { inner }
			| TypeExpression::Grouped { inner, .. } => self.ty(inner),
			TypeExpression::Array { inner, length } => {
				self.ty(inner).or_else(|| self.const_argument(length))
			}
			TypeExpression::QualifiedPath { root, segments } => self
				.qualified_path(
					ast.qualified_root(root),
					ast.list(segments),
					NameUse::Type,
				),
			TypeExpression::Infer | TypeExpression::Never => None,
		}
	}

	fn pattern(&self, pattern: PatId, forms: PatternForms) -> Option<Site> {
		let ast = self.ast;
		if !self.at(ast.pattern_span(pattern)) {
			return None;
		}
		match ast.pattern(pattern) {
			// `const MAX`: a constant, named in the value tier.
			Pattern::Constant { path } => {
				let path = ast.list(path);
				// `const` is explicit syntax: only a constant can follow it.
				// Without it, a qualified path may still become a constructor.
				let used_as = if ast.pattern_span(pattern).start
					< path.first()?.ident.span.start
				{
					NameUse::Constant
				} else {
					NameUse::Pattern
				};
				self.path(path, used_as)
					.map(|site| self.pattern_site(pattern, forms, site))
			}
			Pattern::Or(alternatives) => self.pattern(
				*self.child_by(ast.list(alternatives), |&alternative| {
					ast.pattern_span(alternative)
				})?,
				forms,
			),
			Pattern::Destructure(Destructure::Tuple { elements }) => {
				self.pattern_elements(pattern, ast.list(elements), forms)
			}
			Pattern::Destructure(Destructure::Struct { path, elements }) => {
				self.path(ast.list(path), NameUse::Pattern)
					.map(|site| self.pattern_site(pattern, forms, site))
					.or_else(|| {
						self.pattern_elements(
							pattern,
							ast.list(elements),
							forms,
						)
						.map(|site| Self::inside_pattern(site, pattern))
					})
			}
			Pattern::Destructure(Destructure::NamedStruct {
				path,
				fields,
				open_brace,
			}) => {
				let path = ast.list(path);
				let braces =
					TextSpan::new(open_brace, ast.pattern_span(pattern).end);
				self.path(path, NameUse::Pattern)
					.map(|site| self.pattern_site(pattern, forms, site))
					.or_else(|| {
						self.pattern_fields(
							pattern,
							path,
							ast.list(fields),
							braces,
							forms,
						)
						.map(|site| Self::inside_pattern(site, pattern))
					})
			}
			Pattern::Binding { mutable: false, .. }
				if matches!(forms, PatternForms::Tests) =>
			{
				Some(self.pattern_site(
					pattern,
					forms,
					Site::Reference(ReferenceSite::Name(NameUse::Pattern)),
				))
			}
			// An explicitly mutable binding, or a local's own binding name,
			// declares its name; nothing is looked up.
			Pattern::Binding { .. }
			| Pattern::Wildcard
			| Pattern::Literal(_)
			| Pattern::Error => None,
		}
	}

	fn pattern_site(
		&self,
		pattern: PatId,
		forms: PatternForms,
		site: Site,
	) -> Site {
		let prefix = match site {
			Site::Reference(ReferenceSite::Name(NameUse::Pattern)) => None,
			Site::Reference(ReferenceSite::Segment {
				prefix,
				used_as: NameUse::Pattern,
			}) => Some(prefix),
			_ => return site,
		};
		Site::Pattern(PatternSite {
			target: PatternTarget::Written(pattern),
			prefix,
			forms,
			ancestors: Vec::new(),
		})
	}

	fn inside_pattern(mut site: Site, parent: PatId) -> Site {
		if let Site::Pattern(site) = &mut site {
			site.ancestors.push(parent);
		}
		site
	}

	/// A struct pattern's fields, in their braces: the name of the one at the
	/// cursor, or one not written yet in the room between two, is one of the
	/// fields of what `path` names; after a name's `:` is its pattern.
	fn pattern_fields(
		&self,
		pattern: PatId,
		path: &[PathSegment],
		fields: &[PatternFieldItem],
		braces: TextSpan,
		forms: PatternForms,
	) -> Option<Site> {
		if !self.inside(braces) {
			return None;
		}
		let ast = self.ast;
		let at = self.child_index_by(fields, |item| match *item {
			PatternFieldItem::Field(field) => {
				let end =
					field.pattern.map_or(field.name.span.end, |pattern| {
						ast.pattern_span(pattern).end
					});
				TextSpan::new(field.name.span.start, end)
			}
			PatternFieldItem::Rest(at) => rest_span(at),
		});
		if let Some(at) = at {
			match fields[at] {
				PatternFieldItem::Field(field) if !self.at(field.name.span) => {
					return self.pattern(field.pattern?, forms);
				}
				PatternFieldItem::Field(_) => {}
				PatternFieldItem::Rest(_) => return None,
			}
		}
		let written = (fields.iter().enumerate())
			.filter(|&(index, _)| Some(index) != at)
			.filter_map(|(_, item)| match item {
				PatternFieldItem::Field(field) => Some(field.name.inner),
				PatternFieldItem::Rest(_) => None,
			})
			.collect();
		Some(Site::Slot(SlotSite::PatternField {
			pattern,
			owner: path.last()?.ident.span,
			written,
		}))
	}

	fn pattern_elements(
		&self,
		parent: PatId,
		elements: &[PatternElement],
		forms: PatternForms,
	) -> Option<Site> {
		let ast = self.ast;
		let element = self.child_by(elements, |element| match *element {
			PatternElement::Pattern(pattern) => ast.pattern_span(pattern),
			PatternElement::Rest(at) => rest_span(at),
		});
		match element {
			Some(PatternElement::Pattern(pattern)) => {
				self.pattern(*pattern, forms)
			}
			Some(PatternElement::Rest(_)) => None,
			None => {
				if !self.inside(ast.pattern_span(parent)) {
					return None;
				}
				let at = elements.partition_point(|element| {
					let span = match *element {
						PatternElement::Pattern(pattern) => {
							ast.pattern_span(pattern)
						}
						PatternElement::Rest(at) => rest_span(at),
					};
					span.end < self.offset
				});
				Some(Site::Pattern(PatternSite {
					target: PatternTarget::Insert { parent, at },
					prefix: None,
					forms,
					ancestors: Vec::new(),
				}))
			}
		}
	}

	/// A path: each segment is looked up in `tier` when it is the last, and
	/// as a type when a namespace follows it, as path resolution does
	/// (`try_resolve_path`); the first one is a bare name, and a later one
	/// is looked up in what the segment before it means. A segment not
	/// written yet (`a::`) is the error symbol at the empty span after the
	/// `::`. Type arguments on any segment are types of their own.
	fn path(&self, segments: &[PathSegment], used_as: NameUse) -> Option<Site> {
		let ast = self.ast;
		let index = self.child_index_by(segments, |segment| {
			TextSpan::new(
				segment.ident.span.start,
				ast.type_args_span(segment).end,
			)
		})?;
		if !self.at(segments[index].ident.span) {
			return self.type_args(&segments[index]);
		}
		let used_as = if index + 1 == segments.len() {
			used_as
		} else {
			NameUse::Type
		};
		Some(match index.checked_sub(1) {
			None => Site::Reference(ReferenceSite::Name(used_as)),
			Some(before) => Site::Reference(ReferenceSite::Segment {
				prefix: segments[before].ident.span,
				used_as,
			}),
		})
	}

	/// `<T as Tr>::` and the segments after it: a type and a trait (read
	/// as a bound is), then one of the trait's members, used as `used_as`
	/// when it is the last segment and as a type when more follow. What
	/// follows a member is a member of it, which is not completed.
	fn qualified_path(
		&self,
		root: QualifiedPathRoot,
		segments: &[PathSegment],
		used_as: NameUse,
	) -> Option<Site> {
		let trait_path = self.ast.list(root.trait_path);
		self.ty(root.self_type)
			.or_else(|| self.path(trait_path, NameUse::Bound))
			.or_else(|| {
				let first = segments.first()?;
				if !self.at(first.ident.span) {
					return self.type_args(first);
				}
				Some(Site::Reference(ReferenceSite::TraitMember {
					trait_name: trait_path.last()?.ident.span,
					used_as: match segments.len() {
						1 => used_as,
						_ => NameUse::Type,
					},
				}))
			})
	}

	/// The label of a jump. A label not written yet (`break :`) is the
	/// error symbol at the empty span after the `:`.
	fn label(
		&self,
		label: Option<Spanned<SymbolU32>>,
		jump: Jump,
	) -> Option<Site> {
		self.at(label?.span)
			.then_some(Site::Reference(ReferenceSite::Label(jump)))
	}

	fn type_args(&self, segment: &PathSegment) -> Option<Site> {
		let ast = self.ast;
		let argument = self
			.child_by(ast.list(segment.type_args), |&argument| {
				ast.type_argument_span(argument)
			})?;
		match *argument {
			TypeArgument::Type(ty) => self.ty(ty),
			TypeArgument::Const(constant) => self.const_argument(constant),
		}
	}

	fn const_argument(&self, constant: ConstId) -> Option<Site> {
		let ast = self.ast;
		if !self.at(ast.const_span(constant)) {
			return None;
		}
		match ast.constant(constant) {
			ConstArgument::Path(segments) => {
				self.path(ast.list(segments), NameUse::Constant)
			}
			ConstArgument::QualifiedPath { root, segments } => self
				.qualified_path(
					ast.qualified_root(root),
					ast.list(segments),
					NameUse::Constant,
				),
			ConstArgument::Grouped { inner, .. } => self.ty(inner),
			// A length not written yet (`[u8; ]`).
			ConstArgument::Error => {
				Some(Site::Reference(ReferenceSite::Name(NameUse::Constant)))
			}
			ConstArgument::Literal(_) | ConstArgument::Infer => None,
		}
	}
}
