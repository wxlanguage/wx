//! Completion: what may be written at the cursor, read from the module's
//! syntax, and the names that fit there, from the checker
//! (`notes/lsp-completion-plan.md`).
//!
//! The syntax only says what kind of position the cursor is in, and which
//! declaration it is in, by the span of it the checker keeps; every
//! candidate comes from the checker's own lookups (`Semantics::names_at`,
//! `names_in_signature`, `names_in`, `Body::labels_at`), so nothing is
//! offered that the checker would not accept written there.

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{
	CompletionItem, CompletionItemKind, CompletionParams, CompletionResponse,
	InsertTextFormat,
};
use wx_compiler::ast::{
	AST, AssocBinding, AssocBindingKind, BoundExpression, BoundId, Comment,
	ConstArgument, ConstId, Destructure, EnumEntry, Expression,
	FunctionSignature, FunctionTypeParam, ImplItem, ImportDeclaration,
	ImportEntry, Item, NamedArgument, Path, PathSegment, Pattern,
	PatternElement, PatternFieldItem, QualifiedPathRoot, Separated, Spanned,
	Statement, TraitItem, TypeArgument, TypeExpression, TypeId, TypeParam,
};
use wx_compiler::diagnostics::{SourceSpan, TextSpan};
use wx_compiler::tir::{DeclKind, Definition, LabelKind, NameUse};

use crate::convert::position_to_offset;
use crate::hover;
use crate::snapshot::Snapshot;
use crate::state::ServerState;

/// The names that can be written at the cursor, in a body or a signature.
pub(crate) fn completion(
	state: &ServerState,
	params: &CompletionParams,
) -> Option<CompletionResponse> {
	let position = &params.text_document_position;
	let (snapshot, file) = state.resolve_uri(&position.text_document.uri)?;
	let offset = position_to_offset(
		&snapshot.compilation.files,
		file,
		position.position,
	)?;
	let Position { site, within } =
		position_at(snapshot.compilation.ast(file), offset)?;
	let declaration = match within {
		Within::Signature(Anchor::Name(name)) | Within::Body(name) => {
			snapshot.declared_at(SourceSpan::new(file, name))?
		}
		Within::Signature(Anchor::ImplTarget(target)) => {
			snapshot.impl_with_target(SourceSpan::new(file, target))?
		}
	};
	let sema = &snapshot.sema;
	// A function or a constructor written as a value is inserted as its
	// call, unless the call is written already (`hel|per()`).
	let source = &snapshot.compilation.files.get(file).ok()?.source;
	let called = source[offset as usize..]
		.trim_start_matches(|c: char| c.is_alphanumeric() || c == '_')
		.starts_with('(');
	let insert = match site {
		Site::Name(NameUse::Value)
		| Site::Segment {
			used_as: NameUse::Value,
			..
		} if state.client.completion_snippets && !called => Insert::Call,
		_ => Insert::Name,
	};
	let names = match site {
		Site::Name(used_as) => match within {
			Within::Body(_) => {
				sema.names_at(sema.body_of(declaration)?, offset, used_as)
			}
			Within::Signature(_) => {
				sema.names_in_signature(declaration, used_as)
			}
		},
		// What the prefix means, as checking resolved it; a prefix that did
		// not resolve has nothing after it.
		Site::Segment { prefix, used_as } => {
			let (_, reference) = sema.symbol_at(file, prefix.start)?;
			let Definition::Item(prefix) = reference.definition() else {
				return None;
			};
			sema.names_in(declaration, prefix, used_as)
		}
		Site::Label(jump) => {
			let owner = sema.body_of(declaration)?;
			let body = sema.owner_body(owner)?;
			body.labels_at(offset)
				.into_iter()
				.filter(|&(_, kind)| match jump {
					Jump::Break => true,
					// A `continue` restarts only a loop.
					Jump::Continue => kind == LabelKind::Loop,
				})
				.map(|(label, _)| {
					(
						body.label(label).name.inner,
						Definition::Label { owner, label },
					)
				})
				.collect()
		}
		// A name written twice is reported (E2121), so the ones written are
		// not offered again.
		Site::Argument {
			callee,
			given,
			written,
		} => {
			let (_, reference) = sema.symbol_at(file, callee.start)?;
			sema.argument_names(reference.definition(), given)
				.into_iter()
				.filter(|(name, _)| !written.contains(name))
				.collect()
		}
	};
	let items = names
		.into_iter()
		.map(|(name, definition)| item(snapshot, name, definition, insert))
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
/// (a member's included), an impl's target path (`Semantics::impls`).
#[derive(Clone, Copy)]
pub(crate) enum Anchor {
	Name(TextSpan),
	ImplTarget(TextSpan),
}

/// What an item inserts: its name, or, for a function or a constructor in
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

/// What can be written at the cursor, as completion offers it.
pub(crate) enum Site {
	/// A bare name, used as its `NameUse` says.
	Name(NameUse),
	/// A path's segment after another, used as `used_as` in what the one
	/// before it, written at `prefix`, means.
	Segment { prefix: TextSpan, used_as: NameUse },
	/// The label of a jump.
	Label(Jump),
	/// The name of an argument in a call by name: one of the parameters of
	/// the callee whose last name is written at `callee`, after the first
	/// `given` (a method call's receiver), and not among the `written` ones.
	Argument {
		callee: TextSpan,
		given: usize,
		written: Vec<SymbolU32>,
	},
}

/// One candidate. Locals and type parameters sort before items, as the
/// lookup tries them first.
fn item(
	snapshot: &Snapshot,
	name: SymbolU32,
	definition: Definition,
	insert: Insert,
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
		// An argument's name: what a call by name may give, in order.
		Definition::Parameter { .. } => (CompletionItemKind::VARIABLE, 0),
		Definition::Field { .. } => (CompletionItemKind::FIELD, 0),
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
		// Nothing else is listed: `names_at`, `names_in`, `labels_at` and
		// `argument_names` give locals, type parameters, items, labels,
		// parameters and fields.
		_ => (CompletionItemKind::TEXT, 1),
	};
	// A call's snippet: the cursor between the parentheses, or after them
	// when there is nothing to give.
	let params = match (insert, definition) {
		(Insert::Call, Definition::Item(loc)) => {
			let decls = &snapshot.sema.decls;
			match snapshot.sema.declaration_kind(loc) {
				DeclKind::Function(function) => {
					Some(decls.functions[usize::from(function)].params.len())
				}
				DeclKind::Struct(struct_index) => Some(
					decls.structs[usize::from(struct_index)].field_names.len(),
				),
				_ => None,
			}
		}
		_ => None,
	};
	let insert_text = params.map(|params| match params {
		0 => format!("{label}()"),
		_ => format!("{label}($1)"),
	});
	CompletionItem {
		insert_text_format: insert_text
			.is_some()
			.then_some(InsertTextFormat::SNIPPET),
		insert_text,
		sort_text: Some(format!("{rank}{label}")),
		detail: hover::signature(&snapshot.sema, &snapshot.strings, definition),
		kind: Some(kind),
		label,
		..Default::default()
	}
}

/// What can be written at `offset`, and where: a name being written (its
/// own span reaches the cursor), or a value or type not written yet (an
/// error node the parser kept, or the room between a block's statements or
/// a list's elements), in a declaration's signature or body. `None`
/// anywhere else: in a comment, a declaration's own name, a literal, a
/// member, a segment after a type, a `use` or an `export`.
///
/// One path down the module's syntax: at each level the child at the
/// cursor is found by a binary search of its siblings, which are in source
/// order and do not overlap.
pub(crate) fn position_at(ast: &AST, offset: u32) -> Option<Position> {
	let cursor = Cursor { offset, ast };
	// Inside a comment: its start is the `//` itself, its end the line's.
	let comment = cursor.child(&ast.comments.0);
	if comment.is_some_and(|comment| comment.span.start < offset) {
		return None;
	}
	cursor.item(&cursor.child(&ast.items)?.inner.inner)
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

impl<T: Node> Node for Separated<T> {
	fn span(&self) -> TextSpan {
		self.inner.span()
	}
}

impl Node for PathSegment {
	fn span(&self) -> TextSpan {
		PathSegment::span(self)
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
	offset: u32,
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

	/// `child`, for siblings whose spans are read through the tree (`span`):
	/// the ids of types, bounds and type arguments.
	fn child_by<'s, T>(
		&self,
		siblings: &'s [T],
		span: impl Fn(&T) -> TextSpan,
	) -> Option<&'s T> {
		let index =
			siblings.partition_point(|sibling| span(sibling).end < self.offset);
		let child = siblings.get(index)?;
		self.at(span(child)).then_some(child)
	}

	/// Where in `siblings` the one `child` finds is.
	fn child_index<T: Node>(&self, siblings: &[T]) -> Option<usize> {
		let index = siblings
			.partition_point(|sibling| sibling.span().end < self.offset);
		self.at(siblings.get(index)?.span()).then_some(index)
	}

	fn item(&self, item: &Item) -> Option<Position> {
		match item {
			Item::Function {
				signature, block, ..
			} => self.function(signature, Some(block)),
			Item::FunctionDeclaration { signature, .. }
			| Item::PackageFunction { signature, .. } => self.function(signature, None),
			Item::PackageConst { name, ty, .. }
			| Item::Memory { name, size: ty, .. } => {
				Within::Signature(Anchor::Name(name.span))
					.position(self.ty(*ty))
			}
			Item::PackageType {
				name, type_params, ..
			} => Within::Signature(Anchor::Name(name.span))
				.position(self.type_params(type_params)),
			Item::Global {
				name, ty, value, ..
			}
			| Item::Const {
				name, ty, value, ..
			} => self.constant(name.span, *ty, Some(value)),
			Item::Enum {
				name,
				repr,
				entries,
				..
			} => Within::Signature(Anchor::Name(name.span))
				.position(repr.and_then(|repr| self.ty(repr)))
				.or_else(|| match &self.child(entries)?.inner.inner {
					EnumEntry::Variant(variant) => {
						Within::Body(variant.name.span)
							.position(self.expression(variant.value.as_ref()?))
					}
					EnumEntry::Rest => None,
				}),
			Item::Struct {
				name,
				type_params,
				fields,
				..
			} => Within::Signature(Anchor::Name(name.span)).position(
				self.type_params(type_params)
					.or_else(|| self.ty(self.child(fields)?.inner.inner.ty)),
			),
			Item::TypeAlias {
				name,
				type_params,
				body,
				..
			} => Within::Signature(Anchor::Name(name.span)).position(
				self.type_params(type_params).or_else(|| self.ty((*body)?)),
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
						let member = self.child(members)?;
						self.path(&member.inner.inner.segments, NameUse::Type)
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
					.or_else(|| match &self.child(items)?.inner.inner {
						TraitItem::Function {
							signature, body, ..
						} => self.function(signature, body.as_deref()),
						TraitItem::Const {
							name, ty, value, ..
						} => self.constant(
							name.span,
							Some(*ty),
							value.as_deref(),
						),
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
			} => self.impl_block(type_params, None, target, items),
			Item::TraitImpl {
				type_params,
				trait_name,
				target,
				items,
			} => self.impl_block(type_params, Some(trait_name), target, items),
			Item::Import { items, .. } => {
				let ImportEntry::Declaration { declaration, .. } =
					&self.child(&items.inner)?.inner.inner
				else {
					return None;
				};
				match declaration {
					ImportDeclaration::Function { signature } => {
						self.function(signature, None)
					}
					ImportDeclaration::Global { name, ty, .. }
					| ImportDeclaration::Memory { name, size: ty } => {
						Within::Signature(Anchor::Name(name.span))
							.position(self.ty(*ty))
					}
				}
			}
			Item::Module { items, .. } => {
				self.item(&self.child(&items.inner)?.inner.inner)
			}
			Item::Export { .. }
			| Item::ExportBlock { .. }
			| Item::ModuleDeclaration { .. }
			| Item::PackageInstance { .. }
			| Item::Use { .. } => None,
		}
	}

	/// A function, by its name: its signature, then its body if it has one.
	fn function(
		&self,
		signature: &FunctionSignature,
		body: Option<&Spanned<Expression>>,
	) -> Option<Position> {
		let name = signature.name.span;
		let site = self
			.type_params(&signature.type_params)
			.or_else(|| self.ty(self.child(&signature.params)?.inner.inner.ty))
			.or_else(|| self.ty(signature.result?));
		Within::Signature(Anchor::Name(name))
			.position(site)
			.or_else(|| Within::Body(name).position(self.expression(body?)))
	}

	/// A constant or a global, by its name: its type, then its value.
	fn constant(
		&self,
		name: TextSpan,
		ty: Option<TypeId>,
		value: Option<&Spanned<Expression>>,
	) -> Option<Position> {
		Within::Signature(Anchor::Name(name))
			.position(ty.and_then(|ty| self.ty(ty)))
			.or_else(|| Within::Body(name).position(self.expression(value?)))
	}

	/// An impl: its header, read in its own scope, and its members.
	fn impl_block(
		&self,
		type_params: &[Spanned<TypeParam>],
		trait_name: Option<&Path>,
		target: &Path,
		items: &[Separated<Spanned<ImplItem>>],
	) -> Option<Position> {
		let header = Within::Signature(Anchor::ImplTarget(target.span()));
		let site = self
			.type_params(type_params)
			.or_else(|| self.path(&trait_name?.segments, NameUse::Trait))
			.or_else(|| self.path(&target.segments, NameUse::Type));
		header.position(site).or_else(|| {
			match &self.child(items)?.inner.inner {
				ImplItem::Function {
					signature, block, ..
				} => self.function(signature, Some(block)),
				ImplItem::Constant {
					name, ty, value, ..
				} => self.constant(name.span, *ty, Some(value)),
				// Read in the impl's scope.
				ImplItem::AssocType { ty, .. } => header.position(self.ty(*ty)),
			}
		})
	}

	fn type_params(&self, params: &[Spanned<TypeParam>]) -> Option<Site> {
		match self.child(params)?.inner {
			TypeParam::Type { bounds, .. } => self.bound(bounds?),
			TypeParam::Const { ty, .. } => self.ty(ty),
		}
	}

	fn bound(&self, bound: BoundId) -> Option<Site> {
		if !self.at(self.ast.bound_span(bound)) {
			return None;
		}
		self.bound_expression(self.ast.bound(bound))
	}

	/// A bound names a trait or a typeset; a binding's own name (`Size` in
	/// `where { Size = u32 }`) is a member of it, not completed yet.
	fn bound_expression(&self, bound: BoundExpression) -> Option<Site> {
		let ast = self.ast;
		match bound {
			// A bound the parser expected and did not find.
			BoundExpression::Error => Some(Site::Name(NameUse::Bound)),
			BoundExpression::Path(segments) => {
				self.path(ast.list(segments), NameUse::Bound)
			}
			BoundExpression::WithBindings { path, bindings } => self
				.path(ast.list(path), NameUse::Bound)
				.or_else(|| match self.child(ast.list(bindings))?.kind {
					AssocBindingKind::Equals(ty)
					| AssocBindingKind::ConstRepresentable { ty, .. } => self.ty(ty),
					AssocBindingKind::Bound(bound) => self.bound(bound),
					AssocBindingKind::ConstEquals { value, .. } => {
						self.const_argument(value)
					}
				}),
			BoundExpression::BoundList(bounds) => self.bound(
				*self.child_by(ast.list(bounds), |&b| ast.bound_span(b))?,
			),
		}
	}

	fn statement(&self, statement: &Statement) -> Option<Site> {
		match statement {
			Statement::Expression(expression) => self.expression(expression),
			Statement::LocalDefinition { pattern, ty, value } => self
				.pattern(&pattern.inner, pattern.span)
				.or_else(|| self.ty((*ty)?))
				.or_else(|| self.expression(value)),
		}
	}

	fn expression(&self, expression: &Spanned<Expression>) -> Option<Site> {
		if !self.at(expression.span) {
			return None;
		}
		match &expression.inner {
			// A value the parser expected and did not find.
			Expression::Error => Some(Site::Name(NameUse::Value)),
			Expression::Path(segments) => self.path(segments, NameUse::Value),
			Expression::Block { statements, .. } => {
				match self.child(&statements.inner) {
					Some(statement) => self.statement(&statement.inner.inner),
					// Between statements, inside the braces: a statement
					// can start here. Before them is the keyword and the
					// label, where nothing is looked up.
					None => self
						.inside(statements.span)
						.then_some(Site::Name(NameUse::Value)),
				}
			}
			Expression::Unary { operand, .. } => self.expression(operand),
			Expression::Binary { left, right, .. } => {
				self.expression(left).or_else(|| self.expression(right))
			}
			Expression::Call { callee, arguments } => self
				.expression(callee)
				.or_else(|| self.list(arguments.span, &arguments.inner)),
			Expression::NamedCall { callee, arguments } => {
				let name = match &callee.inner {
					Expression::Path(segments)
					| Expression::QualifiedPath { segments, .. } => {
						segments.last().map(|segment| segment.ident.span)
					}
					_ => None,
				};
				self.expression(callee)
					.or_else(|| self.named(name, 0, arguments))
			}
			Expression::MethodCall(call) => self
				.expression(&call.object)
				.or_else(|| self.type_args(&call.method))
				.or_else(|| {
					self.list(call.arguments.span, &call.arguments.inner)
				}),
			// The object gives the method's receiver.
			Expression::NamedMethodCall(call) => self
				.expression(&call.object)
				.or_else(|| self.type_args(&call.method))
				.or_else(|| {
					self.named(Some(call.method.ident.span), 1, &call.arguments)
				}),
			Expression::ObjectAccess { object, member } => {
				self.expression(object).or_else(|| self.type_args(member))
			}
			Expression::Deref { pointer: value }
			| Expression::AddressOf { value } => self.expression(value),
			Expression::Return { value } => self.expression(value.as_ref()?),
			Expression::Break { label, value } => self
				.label(*label, Jump::Break)
				.or_else(|| self.expression(value.as_ref()?)),
			Expression::Continue { label } => {
				self.label(*label, Jump::Continue)
			}
			Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => self
				.expression(condition)
				.or_else(|| self.expression(then_block))
				.or_else(|| self.expression(else_block.as_ref()?)),
			Expression::Match { scrutinee, arms } => {
				self.expression(scrutinee).or_else(|| {
					let arm = &self.child(arms)?.inner.inner;
					self.pattern(&arm.pattern.inner, arm.pattern.span)
						.or_else(|| self.expression(&arm.body))
				})
			}
			Expression::Loop { block, .. } => self.expression(block),
			Expression::QualifiedPath { root, .. } => {
				self.qualified_root(self.ast.qualified_root(*root))
			}
			Expression::Grouped { inner, .. } => self.ty(*inner),
			Expression::Tuple { elements }
			| Expression::ArrayList { elements } => self.list(expression.span, elements),
			Expression::Ascription { value, ty } => {
				self.expression(value).or_else(|| self.ty(*ty))
			}
			Expression::ArrayRepeat { value, count } => self
				.expression(value)
				.or_else(|| self.const_argument(*count)),
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
	fn list(
		&self,
		delimiters: TextSpan,
		elements: &[Separated<Spanned<Expression>>],
	) -> Option<Site> {
		match self.child(elements) {
			Some(element) => self.expression(&element.inner),
			None => self
				.inside(delimiters)
				.then_some(Site::Name(NameUse::Value)),
		}
	}

	/// A call's named arguments, in their braces: the name of the one at the
	/// cursor, or one not written yet in the room between two, is one of the
	/// callee's parameters (`callee`, its last name, if it has one; `given`,
	/// as `Site::Argument` says); after a name's `:` is its value. Outside
	/// the braces nothing is: a list not closed yet offers no names.
	fn named(
		&self,
		callee: Option<TextSpan>,
		given: usize,
		arguments: &Spanned<Box<[Separated<Spanned<NamedArgument>>]>>,
	) -> Option<Site> {
		if !self.inside(arguments.span) {
			return None;
		}
		let at = self.child_index(&arguments.inner);
		if let Some(at) = at {
			let argument = &arguments.inner[at].inner.inner;
			if !self.at(argument.name.span) {
				return self.expression(argument.value.as_deref()?);
			}
		}
		let written = (arguments.inner.iter().enumerate())
			.filter(|&(index, _)| Some(index) != at)
			.map(|(_, argument)| argument.inner.inner.name.inner)
			.collect();
		Some(Site::Argument {
			callee: callee?,
			given,
			written,
		})
	}

	fn ty(&self, ty: TypeId) -> Option<Site> {
		let ast = self.ast;
		if !self.at(ast.type_span(ty)) {
			return None;
		}
		match ast.ty(ty) {
			// A type the parser expected and did not find.
			TypeExpression::Error => Some(Site::Name(NameUse::Type)),
			TypeExpression::Path(segments) => {
				self.path(ast.list(segments), NameUse::Type)
			}
			TypeExpression::Tuple { elements } => self
				.ty(*self
					.child_by(ast.list(elements), |&e| ast.type_span(e))?),
			TypeExpression::Function { params, result } => self
				.child(ast.list(params))
				.and_then(|param| self.ty(param.ty))
				.or_else(|| self.ty(result?)),
			TypeExpression::Pointer { inner, .. }
			| TypeExpression::Slice { inner }
			| TypeExpression::Grouped { inner, .. } => self.ty(inner),
			TypeExpression::Array { inner, length } => {
				self.ty(inner).or_else(|| self.const_argument(length))
			}
			TypeExpression::QualifiedPath { root, .. } => {
				self.qualified_root(ast.qualified_root(root))
			}
			TypeExpression::Infer | TypeExpression::Never => None,
		}
	}

	fn pattern(&self, pattern: &Pattern, span: TextSpan) -> Option<Site> {
		if !self.at(span) {
			return None;
		}
		match pattern {
			// `const MAX`: a constant, named in the value tier.
			Pattern::Constant { path } => self.path(path, NameUse::Value),
			Pattern::Or(alternatives) => {
				let alternative = &self.child(alternatives)?.inner;
				self.pattern(&alternative.inner, alternative.span)
			}
			Pattern::Destructure(Destructure::Tuple { elements }) => {
				self.pattern_elements(elements)
			}
			Pattern::Destructure(Destructure::Struct { path, elements }) => {
				self.path(path, NameUse::Value)
					.or_else(|| self.pattern_elements(elements))
			}
			Pattern::Destructure(Destructure::NamedStruct { path, fields }) => {
				self.path(path, NameUse::Value).or_else(|| {
					match &self.child(fields)?.inner.inner {
						PatternFieldItem::Field(field) => {
							let pattern = field.pattern.as_ref()?;
							self.pattern(&pattern.inner, pattern.span)
						}
						PatternFieldItem::Rest => None,
					}
				})
			}
			// A binding declares its name; nothing is looked up.
			Pattern::Binding { .. }
			| Pattern::Wildcard
			| Pattern::Literal(_)
			| Pattern::Error => None,
		}
	}

	fn pattern_elements(
		&self,
		elements: &[Separated<Spanned<PatternElement>>],
	) -> Option<Site> {
		let element = &self.child(elements)?.inner;
		match &element.inner {
			PatternElement::Pattern(pattern) => {
				self.pattern(pattern, element.span)
			}
			PatternElement::Rest => None,
		}
	}

	/// A path: each segment is looked up in `tier` when it is the last, and
	/// as a type when a namespace follows it, as path resolution does
	/// (`try_resolve_path`); the first one is a bare name, and a later one
	/// is looked up in what the segment before it means. A segment not
	/// written yet (`a::`) is the error symbol at the empty span after the
	/// `::`. Type arguments on any segment are types of their own.
	fn path(&self, segments: &[PathSegment], used_as: NameUse) -> Option<Site> {
		let index = self.child_index(segments)?;
		if !self.at(segments[index].ident.span) {
			return self.type_args(&segments[index]);
		}
		let used_as = if index + 1 == segments.len() {
			used_as
		} else {
			NameUse::Type
		};
		Some(match index.checked_sub(1) {
			None => Site::Name(used_as),
			Some(before) => Site::Segment {
				prefix: segments[before].ident.span,
				used_as,
			},
		})
	}

	/// `<T as Tr>` before a path's segments: a type and a trait (read as a
	/// bound is). What
	/// follows it is a member of the type, which is not completed yet.
	fn qualified_root(&self, root: QualifiedPathRoot) -> Option<Site> {
		self.ty(root.self_type).or_else(|| {
			self.path(self.ast.list(root.trait_path), NameUse::Bound)
		})
	}

	/// The label of a jump. A label not written yet (`break :`) is the
	/// error symbol at the empty span after the `:`.
	fn label(
		&self,
		label: Option<Spanned<SymbolU32>>,
		jump: Jump,
	) -> Option<Site> {
		self.at(label?.span).then_some(Site::Label(jump))
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
				self.path(ast.list(segments), NameUse::Value)
			}
			ConstArgument::QualifiedPath { root, .. } => {
				self.qualified_root(ast.qualified_root(root))
			}
			ConstArgument::Grouped { inner, .. } => self.ty(inner),
			ConstArgument::Literal(_) | ConstArgument::Infer => None,
		}
	}
}
