//! A file's tree as nested text, for the parser's tests: ids, lists and
//! names resolved, so a test states the tree it expects (`a + b * c` is
//! `(+ a (* b c))`) and a snapshot reads as the syntax it parsed, whatever
//! the columns hold.
//!
//! Items, statements, expressions and patterns print as S-expressions. What
//! is written at the type level (types, bounds, constant arguments and
//! paths) prints as canonical source text, `heap::&[u8]` or `Memory where
//! { Size = u32 }`, an atom of the S-expression around it. Literals print
//! as written. Spans are left out: the suite asserts them where they matter.

use super::*;

/// One node of the printed tree: an atom, or a parenthesized list.
pub(super) enum Sexp {
	Atom(String),
	List(Vec<Sexp>),
}

impl Sexp {
	fn atom(text: impl Into<String>) -> Self {
		Sexp::Atom(text.into())
	}

	/// A list whose head is `head`.
	fn head(head: &str, children: impl IntoIterator<Item = Sexp>) -> Self {
		let mut items = vec![Sexp::atom(head)];
		items.extend(children);
		Sexp::List(items)
	}

	/// On one line.
	pub(super) fn flat(&self) -> String {
		let mut out = String::new();
		self.write_flat(&mut out);
		out
	}

	fn write_flat(&self, out: &mut String) {
		match self {
			Sexp::Atom(text) => out.push_str(text),
			Sexp::List(items) => {
				out.push('(');
				for (index, item) in items.iter().enumerate() {
					if index > 0 {
						out.push(' ');
					}
					item.write_flat(out);
				}
				out.push(')');
			}
		}
	}

	/// Within `width` columns where it can be: a list that does not fit
	/// keeps its leading atoms on its first line and puts every other child
	/// on a line of its own, two spaces further in.
	pub(super) fn pretty(&self, width: usize) -> String {
		let mut out = String::new();
		self.write_pretty(&mut out, 0, width);
		out
	}

	fn write_pretty(&self, out: &mut String, indent: usize, width: usize) {
		let flat = self.flat();
		let Sexp::List(items) = self else {
			out.push_str(&flat);
			return;
		};
		if indent + flat.len() <= width {
			out.push_str(&flat);
			return;
		}
		out.push('(');
		let leading = items
			.iter()
			.take_while(|item| matches!(item, Sexp::Atom(_)))
			.count();
		for (index, item) in items[..leading].iter().enumerate() {
			if index > 0 {
				out.push(' ');
			}
			item.write_flat(out);
		}
		for item in &items[leading..] {
			out.push('\n');
			out.extend(std::iter::repeat_n(' ', indent + 2));
			item.write_pretty(out, indent + 2, width);
		}
		out.push(')');
	}
}

/// Prints the nodes of one file's tree.
pub(super) struct Printer<'a> {
	ast: &'a AST,
	strings: &'a StringInterner,
	/// The file's text, where a literal's spelling is read.
	source: &'a str,
}

impl<'a> Printer<'a> {
	pub(super) fn new(
		ast: &'a AST,
		strings: &'a StringInterner,
		source: &'a str,
	) -> Self {
		Self {
			ast,
			strings,
			source,
		}
	}

	/// The file's items, in written order.
	pub(super) fn file(&self) -> Vec<Sexp> {
		self.ast
			.list(self.ast.root)
			.iter()
			.map(|item| self.item(item))
			.collect()
	}

	fn name(&self, symbol: SymbolU32) -> &'a str {
		self.strings
			.resolve(symbol)
			.expect("symbol was interned by this parse")
	}

	fn text(&self, span: TextSpan) -> &'a str {
		&self.source[span.start as usize..span.end as usize]
	}

	fn label(&self, label: Option<Spanned<SymbolU32>>) -> Option<Sexp> {
		label.map(|label| Sexp::atom(format!(":{}", self.name(label.inner))))
	}

	fn visibility(&self, pub_span: Option<TextSpan>) -> Option<Sexp> {
		pub_span.map(|_| Sexp::atom("pub"))
	}

	// ── Items ───────────────────────────────────────────────────────────────

	fn item(&self, item: &Item) -> Sexp {
		match *item {
			Item::Function {
				pub_span,
				attributes,
				signature,
				block,
			} => self.function(
				"func",
				pub_span,
				attributes,
				&signature,
				Some(block),
			),
			Item::FunctionDeclaration {
				pub_span,
				attributes,
				signature,
			} => self.function("func", pub_span, attributes, &signature, None),
			Item::PackageFunction {
				pub_span,
				attributes,
				signature,
				..
			} => self.function(
				"package-func",
				pub_span,
				attributes,
				&signature,
				None,
			),
			Item::PackageConst {
				pub_span,
				attributes,
				name,
				ty,
				..
			} => Sexp::head(
				"package-const",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain([Sexp::head("type", [Sexp::atom(self.ty(ty))])]),
			),
			Item::PackageType {
				pub_span,
				attributes,
				name,
				type_params,
				..
			} => Sexp::head(
				"package-type",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.type_params(type_params)),
			),
			Item::Global {
				pub_span,
				mut_span,
				name,
				ty,
				value,
				attributes,
			} => Sexp::head(
				"global",
				self.visibility(pub_span)
					.into_iter()
					.chain(mut_span.map(|_| Sexp::atom("mut")))
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.annotation(ty))
					.chain([self.expr(value)]),
			),
			Item::Export { entry } => {
				Sexp::head("export", [self.export_entry(&entry)])
			}
			Item::ExportBlock { entries, .. } => Sexp::head(
				"export-block",
				self.ast
					.list(entries)
					.iter()
					.map(|entry| self.export_entry(entry)),
			),
			Item::Import {
				external_name,
				internal_name,
				entries,
				..
			} => Sexp::head(
				"import",
				[
					Sexp::atom(self.text(external_name)),
					Sexp::atom(self.name(internal_name.inner)),
				]
				.into_iter()
				.chain(
					self.ast
						.list(entries)
						.iter()
						.map(|entry| self.import_entry(entry)),
				),
			),
			Item::Enum {
				pub_span,
				repr,
				name,
				entries,
				attributes,
			} => Sexp::head(
				"enum",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(repr.map(|repr| {
						Sexp::head("repr", [Sexp::atom(self.ty(repr))])
					}))
					.chain(self.ast.list(entries).iter().map(|entry| {
						match *entry {
							EnumEntry::Variant(EnumVariant {
								name,
								value: None,
							}) => Sexp::atom(self.name(name.inner)),
							EnumEntry::Variant(EnumVariant {
								name,
								value: Some(value),
							}) => Sexp::head(
								"=",
								[
									Sexp::atom(self.name(name.inner)),
									self.expr(value),
								],
							),
							EnumEntry::Rest => Sexp::atom(".."),
						}
					})),
			),
			Item::InherentImpl {
				type_params,
				target,
				items,
			} => Sexp::head(
				"impl",
				[Sexp::atom(self.type_path(target.segments))]
					.into_iter()
					.chain(self.type_params(type_params))
					.chain(
						self.ast
							.list(items)
							.iter()
							.map(|item| self.impl_item(item)),
					),
			),
			Item::TraitImpl {
				type_params,
				trait_name,
				target,
				items,
			} => Sexp::head(
				"impl",
				[
					Sexp::atom(self.type_path(trait_name.segments)),
					Sexp::atom("for"),
					Sexp::atom(self.type_path(target.segments)),
				]
				.into_iter()
				.chain(self.type_params(type_params))
				.chain(
					self.ast
						.list(items)
						.iter()
						.map(|item| self.impl_item(item)),
				),
			),
			Item::Struct {
				pub_span,
				attributes,
				name,
				type_params,
				fields,
			} => Sexp::head(
				"struct",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.type_params(type_params))
					.chain(self.ast.list(fields).iter().map(|field| {
						Sexp::head(
							"field",
							self.visibility(field.pub_span)
								.into_iter()
								.chain(self.bound_to(field.binding, field.ty)),
						)
					})),
			),
			Item::Memory {
				pub_span,
				attributes,
				name,
				size,
			} => Sexp::head(
				"memory",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain([Sexp::atom(self.ty(size))]),
			),
			Item::Const {
				pub_span,
				name,
				ty,
				value,
				attributes,
			} => Sexp::head(
				"const",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.annotation(ty))
					.chain([self.expr(value)]),
			),
			Item::Module {
				pub_span,
				name,
				items,
				..
			} => Sexp::head(
				"mod",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(
						self.ast.list(items).iter().map(|item| self.item(item)),
					),
			),
			Item::ModuleDeclaration { pub_span, name } => Sexp::head(
				"mod-decl",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))]),
			),
			Item::PackageInstance {
				pub_span,
				package,
				alias,
			} => Sexp::head(
				"package",
				self.visibility(pub_span).into_iter().chain([
					Sexp::atom(self.text(package)),
					Sexp::atom(self.name(alias.inner)),
				]),
			),
			Item::Trait {
				pub_span,
				attributes,
				name,
				supertraits,
				items,
			} => Sexp::head(
				"trait",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(supertraits.map(|bound| {
						Sexp::head(
							"supertraits",
							[Sexp::atom(self.bound(bound))],
						)
					}))
					.chain(
						self.ast
							.list(items)
							.iter()
							.map(|item| self.trait_item(item)),
					),
			),
			Item::TypeSet {
				pub_span,
				attributes,
				name,
				bounds,
				members,
			} => Sexp::head(
				"typeset",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(bounds.map(|bound| {
						Sexp::head("bounds", [Sexp::atom(self.bound(bound))])
					}))
					.chain(self.ast.list(members).iter().map(|member| {
						Sexp::atom(self.type_path(member.segments))
					})),
			),
			Item::Use { pub_span, tree } => Sexp::head(
				"use",
				self.visibility(pub_span)
					.into_iter()
					.chain([self.use_tree(String::new(), tree)]),
			),
			Item::TypeAlias {
				pub_span,
				name,
				type_params,
				body,
				attributes,
			} => Sexp::head(
				"type",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.type_params(type_params))
					.chain(body.map(|body| Sexp::atom(self.ty(body)))),
			),
		}
	}

	fn impl_item(&self, item: &ImplItem) -> Sexp {
		match *item {
			ImplItem::Function {
				pub_span,
				attributes,
				signature,
				block,
			} => self.function(
				"func",
				pub_span,
				attributes,
				&signature,
				Some(block),
			),
			ImplItem::Constant {
				pub_span,
				name,
				ty,
				value,
				attributes,
			} => Sexp::head(
				"const",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain(self.annotation(ty))
					.chain([self.expr(value)]),
			),
			ImplItem::AssocType {
				pub_span,
				name,
				ty,
				attributes,
			} => Sexp::head(
				"type",
				self.visibility(pub_span)
					.into_iter()
					.chain([Sexp::atom(self.name(name.inner))])
					.chain(self.attributes(attributes))
					.chain([Sexp::atom(self.ty(ty))]),
			),
		}
	}

	fn trait_item(&self, item: &TraitItem) -> Sexp {
		match *item {
			TraitItem::Function {
				attributes,
				signature,
				body,
			} => self.function("func", None, attributes, &signature, body),
			TraitItem::Const {
				name,
				attributes,
				ty,
				value,
			} => Sexp::head(
				"const",
				[Sexp::atom(self.name(name.inner))]
					.into_iter()
					.chain(self.attributes(attributes))
					.chain(self.annotation(Some(ty)))
					.chain(value.map(|value| self.expr(value))),
			),
			TraitItem::AssociatedType {
				name,
				attributes,
				bounds,
				value,
			} => Sexp::head(
				"type",
				[Sexp::atom(self.name(name.inner))]
					.into_iter()
					.chain(self.attributes(attributes))
					.chain(bounds.map(|bound| {
						Sexp::head("bounds", [Sexp::atom(self.bound(bound))])
					}))
					.chain(value.map(|value| {
						Sexp::head("default", [Sexp::atom(self.ty(value))])
					})),
			),
		}
	}

	/// `(head pub name (attr ..) (type-params ..) (params ..) (result ..)
	/// (block ..))`, each part only where it is written.
	fn function(
		&self,
		head: &str,
		pub_span: Option<TextSpan>,
		attributes: List<Attribute>,
		signature: &FunctionSignature,
		block: Option<BlockId>,
	) -> Sexp {
		Sexp::head(
			head,
			self.visibility(pub_span)
				.into_iter()
				.chain(self.signature(signature, attributes))
				.chain(block.map(|block| self.block("block", None, block))),
		)
	}

	/// A signature's name and parts, with the attributes after the name.
	fn signature(
		&self,
		signature: &FunctionSignature,
		attributes: List<Attribute>,
	) -> impl Iterator<Item = Sexp> + use<'_, 'a> {
		let params = self.ast.list(signature.params).iter().map(|param| {
			match self.bound_to(param.binding, param.ty) {
				mut parts if parts.len() == 1 => parts.remove(0),
				parts => Sexp::List(parts),
			}
		});
		[Sexp::atom(self.name(signature.name.inner))]
			.into_iter()
			.chain(self.attributes(attributes))
			.chain(self.type_params(signature.type_params))
			.chain([Sexp::head("params", params)])
			.chain(signature.result.map(|result| {
				Sexp::head("result", [Sexp::atom(self.ty(result))])
			}))
	}

	/// What a parameter or a field is bound to, then its type: `T` alone
	/// when nothing is bound, else `x T`, `mut x T` or `_ T`.
	fn bound_to(&self, binding: Option<Binding>, ty: TypeId) -> Vec<Sexp> {
		let ty = Sexp::atom(self.ty(ty));
		match binding {
			None => vec![ty],
			Some(Binding::Wildcard(_)) => vec![Sexp::atom("_"), ty],
			Some(Binding::Name { mut_span, name }) => mut_span
				.map(|_| Sexp::atom("mut"))
				.into_iter()
				.chain([Sexp::atom(self.name(name.inner)), ty])
				.collect(),
		}
	}

	/// `(type T)`, when a type is written.
	fn annotation(&self, ty: Option<TypeId>) -> Option<Sexp> {
		ty.map(|ty| Sexp::head("type", [Sexp::atom(self.ty(ty))]))
	}

	fn attributes(
		&self,
		attributes: List<Attribute>,
	) -> impl Iterator<Item = Sexp> + use<'_, 'a> {
		self.ast.list(attributes).iter().map(|attribute| {
			let name = Sexp::atom(self.name(attribute.name.inner));
			match attribute.value {
				AttributeValue::Word => Sexp::head("attr", [name]),
				AttributeValue::Named(arguments) => Sexp::head(
					"attr",
					[name].into_iter().chain(self.named(arguments)),
				),
			}
		})
	}

	/// `(type-params T (U Bound) (const N u32))`, when any is written.
	fn type_params(&self, params: List<TypeParam>) -> Option<Sexp> {
		let params = self.ast.list(params);
		(!params.is_empty()).then(|| {
			Sexp::head(
				"type-params",
				params.iter().map(|param| match *param {
					TypeParam::Type { name, bounds: None } => {
						Sexp::atom(self.name(name.inner))
					}
					TypeParam::Type {
						name,
						bounds: Some(bounds),
					} => Sexp::List(vec![
						Sexp::atom(self.name(name.inner)),
						Sexp::atom(self.bound(bounds)),
					]),
					TypeParam::Const { name, ty, .. } => Sexp::head(
						"const",
						[
							Sexp::atom(self.name(name.inner)),
							Sexp::atom(self.ty(ty)),
						],
					),
				}),
			)
		})
	}

	fn export_entry(&self, entry: &ExportEntry) -> Sexp {
		let name = Sexp::atom(self.name(entry.name.inner));
		match entry.alias {
			None => name,
			Some(alias) => Sexp::List(vec![name, Sexp::atom(self.text(alias))]),
		}
	}

	fn import_entry(&self, entry: &ImportEntry) -> Sexp {
		match *entry {
			ImportEntry::Declaration {
				external_name,
				declaration,
			} => {
				let external =
					external_name.map(|name| Sexp::atom(self.text(name)));
				match declaration {
					ImportDeclaration::Function { signature } => Sexp::head(
						"func",
						external
							.into_iter()
							.chain(self.signature(&signature, List::EMPTY)),
					),
					ImportDeclaration::Global { mut_span, name, ty } => {
						Sexp::head(
							"global",
							external
								.into_iter()
								.chain(mut_span.map(|_| Sexp::atom("mut")))
								.chain([
									Sexp::atom(self.name(name.inner)),
									Sexp::head(
										"type",
										[Sexp::atom(self.ty(ty))],
									),
								]),
						)
					}
					ImportDeclaration::Memory { name, size } => Sexp::head(
						"memory",
						external.into_iter().chain([
							Sexp::atom(self.name(name.inner)),
							Sexp::atom(self.ty(size)),
						]),
					),
				}
			}
			ImportEntry::Use { pub_span, tree } => Sexp::head(
				"use",
				self.visibility(pub_span)
					.into_iter()
					.chain([self.use_tree(String::new(), tree)]),
			),
		}
	}

	/// A `use` tree, the path walked to so far in `prefix`: a straight path
	/// is one atom (`math::add`, `math::*`), a rename is `(as math::add
	/// plus)`, and a group is `(group math::geom ..)` of its branches.
	fn use_tree(&self, mut prefix: String, tree: UseTreeId) -> Sexp {
		match self.ast.use_tree(tree) {
			UseTree::Glob { segment } => {
				prefix.push_str(self.name(segment.inner));
				prefix.push_str("::*");
				Sexp::Atom(prefix)
			}
			UseTree::Name {
				segment,
				alias: None,
			} => {
				prefix.push_str(self.name(segment.inner));
				Sexp::Atom(prefix)
			}
			UseTree::Name {
				segment,
				alias: Some(alias),
			} => {
				prefix.push_str(self.name(segment.inner));
				Sexp::head(
					"as",
					[Sexp::Atom(prefix), Sexp::atom(self.name(alias.inner))],
				)
			}
			UseTree::Path { segment, rest } => {
				prefix.push_str(self.name(segment.inner));
				prefix.push_str("::");
				self.use_tree(prefix, rest)
			}
			UseTree::Group {
				segment, branches, ..
			} => {
				prefix.push_str(self.name(segment.inner));
				Sexp::head(
					"group",
					[Sexp::Atom(prefix)].into_iter().chain(
						self.ast
							.ids(branches)
							.map(|branch| self.use_tree(String::new(), branch)),
					),
				)
			}
		}
	}

	// ── Blocks and statements ───────────────────────────────────────────────

	/// `(head :label (; statement) .. tail)`: each statement as written,
	/// then the tail, the block's value, bare.
	fn block(
		&self,
		head: &str,
		label: Option<Spanned<SymbolU32>>,
		block: BlockId,
	) -> Sexp {
		let Block { statements, tail } = self.ast.block(block);
		Sexp::head(
			head,
			self.label(label)
				.into_iter()
				.chain(
					self.ast
						.list(statements)
						.iter()
						.map(|&statement| self.statement(statement)),
				)
				.chain(tail.map(|tail| self.expr(tail))),
		)
	}

	fn statement(&self, statement: StmtId) -> Sexp {
		match self.ast.statement(statement) {
			Statement::Expression(expr) => Sexp::head(";", [self.expr(expr)]),
			Statement::LocalDefinition { pattern, ty, value } => Sexp::head(
				"local",
				[self.pattern(pattern)]
					.into_iter()
					.chain(self.annotation(ty))
					.chain([self.expr(value)]),
			),
		}
	}

	// ── Expressions ─────────────────────────────────────────────────────────

	pub(super) fn expr(&self, expr: ExprId) -> Sexp {
		match self.ast.expr(expr) {
			Expression::Error => Sexp::atom("<error>"),
			Expression::Int { value } => Sexp::atom(value.to_string()),
			Expression::Float | Expression::String | Expression::Char => {
				Sexp::atom(self.text(self.ast.expr_span(expr)))
			}
			Expression::Placeholder => Sexp::atom("_"),
			// `u` keeps a unary `-` apart from a binary one.
			Expression::Unary { operator, operand } => {
				Sexp::head(&format!("u{operator}"), [self.expr(operand)])
			}
			Expression::Binary {
				operator,
				left,
				right,
				..
			} => Sexp::head(
				operator.as_str(),
				[self.expr(left), self.expr(right)],
			),
			Expression::Call {
				callee, arguments, ..
			} => Sexp::head(
				"call",
				[self.expr(callee)].into_iter().chain(
					self.ast
						.list(arguments)
						.iter()
						.map(|&argument| self.expr(argument)),
				),
			),
			Expression::NamedCall {
				callee, arguments, ..
			} => Sexp::head(
				"call",
				[
					self.expr(callee),
					Sexp::head("named", self.named(arguments)),
				],
			),
			Expression::ObjectAccess { object, member } => Sexp::head(
				".",
				[
					self.expr(object),
					Sexp::Atom(self.segment(&self.ast.segment(member), "::")),
				],
			),
			Expression::Deref { pointer } => {
				Sexp::head(".*", [self.expr(pointer)])
			}
			Expression::AddressOf { value } => {
				Sexp::head(".&", [self.expr(value)])
			}
			Expression::Return { value } => {
				Sexp::head("return", value.map(|value| self.expr(value)))
			}
			Expression::Block { label, block } => {
				self.block("block", label, block)
			}
			Expression::Break { label, value } => Sexp::head(
				"break",
				self.label(label)
					.into_iter()
					.chain(value.map(|value| self.expr(value))),
			),
			Expression::Continue { label } => {
				Sexp::head("continue", self.label(label))
			}
			Expression::IfElse {
				condition,
				then_block,
				else_block,
			} => Sexp::head(
				"if",
				[self.expr(condition), self.block("block", None, then_block)]
					.into_iter()
					.chain(else_block.map(|block| self.expr(block))),
			),
			Expression::Match { scrutinee, arms } => Sexp::head(
				"match",
				[self.expr(scrutinee)].into_iter().chain(
					self.ast.list(arms).iter().map(|arm| {
						Sexp::head(
							"=>",
							[self.pattern(arm.pattern), self.expr(arm.body)],
						)
					}),
				),
			),
			Expression::Loop { label, block } => {
				self.block("loop", label, block)
			}
			Expression::Path(segments) => {
				Sexp::Atom(self.path(self.ast.list(segments), "::"))
			}
			Expression::QualifiedPath { root, segments } => Sexp::Atom(
				self.rooted(&self.qualified_root(root), segments, "::"),
			),
			Expression::Grouped { inner, segments } => Sexp::Atom(self.rooted(
				&format!("<{}>", self.ty(inner)),
				segments,
				"::",
			)),
			Expression::Tuple { elements } => Sexp::head(
				"tuple",
				self.ast
					.list(elements)
					.iter()
					.map(|&element| self.expr(element)),
			),
			Expression::Ascription { value, ty } => {
				Sexp::head(":", [self.expr(value), Sexp::atom(self.ty(ty))])
			}
			Expression::ArrayList { elements } => Sexp::head(
				"array",
				self.ast
					.list(elements)
					.iter()
					.map(|&element| self.expr(element)),
			),
			Expression::ArrayRepeat { value, count } => Sexp::head(
				"repeat",
				[self.expr(value), Sexp::atom(self.constant(count))],
			),
			Expression::Index { object, index } => {
				Sexp::head("index", [self.expr(object), self.expr(index)])
			}
		}
	}

	/// A named list's entries: `(x value)`, or `x` for the shorthand.
	fn named(
		&self,
		arguments: List<NamedArgument>,
	) -> impl Iterator<Item = Sexp> + use<'_, 'a> {
		self.ast.list(arguments).iter().map(|argument| {
			let name = Sexp::atom(self.name(argument.name.inner));
			match argument.value {
				None => name,
				Some(value) => Sexp::List(vec![name, self.expr(value)]),
			}
		})
	}

	// ── Patterns ────────────────────────────────────────────────────────────

	/// A binding is `x` or `(mut x)`, a constant `(const MAX)`, a
	/// destructure `(tuple ..)`, `(Point a ..)` or `(Point (named x (y b)
	/// ..))`.
	pub(super) fn pattern(&self, pattern: PatId) -> Sexp {
		match self.ast.pattern(pattern) {
			Pattern::Wildcard => Sexp::atom("_"),
			Pattern::Binding {
				mutable: false,
				name,
			} => Sexp::atom(self.name(name.inner)),
			Pattern::Binding {
				mutable: true,
				name,
			} => Sexp::head("mut", [Sexp::atom(self.name(name.inner))]),
			Pattern::Constant { path } => Sexp::head(
				"const",
				[Sexp::Atom(self.path(self.ast.list(path), "::"))],
			),
			Pattern::Literal(literal) => Sexp::Atom(
				self.literal(literal, self.ast.pattern_span(pattern)),
			),
			Pattern::Or(alternatives) => Sexp::head(
				"|",
				self.ast
					.list(alternatives)
					.iter()
					.map(|&alternative| self.pattern(alternative)),
			),
			Pattern::Destructure(Destructure::Tuple { elements }) => {
				Sexp::head("tuple", self.pattern_elements(elements))
			}
			Pattern::Destructure(Destructure::Struct { path, elements }) => {
				Sexp::head(
					&self.path(self.ast.list(path), "::"),
					self.pattern_elements(elements),
				)
			}
			Pattern::Destructure(Destructure::NamedStruct { path, fields }) => {
				let fields =
					self.ast.list(fields).iter().map(|field| match *field {
						PatternFieldItem::Field(PatternField {
							name,
							pattern: None,
						}) => Sexp::atom(self.name(name.inner)),
						PatternFieldItem::Field(PatternField {
							name,
							pattern: Some(pattern),
						}) => Sexp::List(vec![
							Sexp::atom(self.name(name.inner)),
							self.pattern(pattern),
						]),
						PatternFieldItem::Rest(_) => Sexp::atom(".."),
					});
				Sexp::head(
					&self.path(self.ast.list(path), "::"),
					[Sexp::head("named", fields)],
				)
			}
			Pattern::Error => Sexp::atom("<error>"),
		}
	}

	fn pattern_elements(
		&self,
		elements: List<PatternElement>,
	) -> impl Iterator<Item = Sexp> + use<'_, 'a> {
		self.ast
			.list(elements)
			.iter()
			.map(|element| match *element {
				PatternElement::Pattern(pattern) => self.pattern(pattern),
				PatternElement::Rest(_) => Sexp::atom(".."),
			})
	}

	/// A literal as written; a number by its value.
	fn literal(&self, literal: Literal, span: TextSpan) -> String {
		match literal {
			Literal::Int(value) => value.to_string(),
			Literal::NegInt(value) => format!("-{value}"),
			Literal::Char | Literal::Float | Literal::String => {
				self.text(span).to_string()
			}
		}
	}

	// ── The type level, as source text ──────────────────────────────────────

	pub(super) fn ty(&self, ty: TypeId) -> String {
		match self.ast.ty(ty) {
			TypeExpression::Error => "<error>".to_string(),
			TypeExpression::Infer => "_".to_string(),
			TypeExpression::Never => "!".to_string(),
			TypeExpression::Path(segments) => self.type_path(segments),
			TypeExpression::Tuple { elements } => {
				match self.ast.list(elements) {
					// The comma keeps a tuple of one apart from its element.
					[element] => format!("({},)", self.ty(*element)),
					elements => format!("({})", self.types(elements)),
				}
			}
			TypeExpression::Function { params, result } => {
				let params = self
					.ast
					.list(params)
					.iter()
					.map(|param| match param.name {
						Some(name) => {
							format!(
								"{}: {}",
								self.name(name.inner),
								self.ty(param.ty)
							)
						}
						None => self.ty(param.ty),
					})
					.collect::<Vec<_>>()
					.join(", ");
				match result {
					Some(result) => {
						format!("func({params}) -> {}", self.ty(result))
					}
					None => format!("func({params})"),
				}
			}
			TypeExpression::Pointer {
				ownership,
				memory,
				inner,
			} => {
				let memory = memory.map_or(String::new(), |memory| {
					format!("{}::", self.type_path(memory))
				});
				let sigil = match ownership {
					Ownership::Exclusive => '*',
					Ownership::Shared => '&',
				};
				format!("{memory}{sigil}{}", self.ty(inner))
			}
			TypeExpression::Slice { inner } => format!("[{}]", self.ty(inner)),
			TypeExpression::Array { inner, length } => {
				format!("[{}; {}]", self.ty(inner), self.constant(length))
			}
			TypeExpression::QualifiedPath { root, segments } => {
				self.rooted(&self.qualified_root(root), segments, "")
			}
			TypeExpression::Grouped { inner, segments } => {
				self.rooted(&format!("<{}>", self.ty(inner)), segments, "")
			}
		}
	}

	fn types(&self, types: &[TypeId]) -> String {
		types
			.iter()
			.map(|&ty| self.ty(ty))
			.collect::<Vec<_>>()
			.join(", ")
	}

	fn bound(&self, bound: BoundId) -> String {
		match self.ast.bound(bound) {
			BoundExpression::Error => "<error>".to_string(),
			BoundExpression::Path(segments) => self.type_path(segments),
			BoundExpression::WithBindings { path, bindings } => {
				let bindings = self
					.ast
					.list(bindings)
					.iter()
					.map(|binding| {
						let name = self.name(binding.name.inner);
						match binding.kind {
							AssocBindingKind::Equals(ty) => {
								format!("{name} = {}", self.ty(ty))
							}
							AssocBindingKind::Bound(bound) => {
								format!("{name}: {}", self.bound(bound))
							}
							AssocBindingKind::ConstRepresentable {
								ty, ..
							} => {
								format!("const {name}: {}", self.ty(ty))
							}
							AssocBindingKind::ConstEquals { value, .. } => {
								format!(
									"const {name} = {}",
									self.constant(value)
								)
							}
						}
					})
					.collect::<Vec<_>>()
					.join(", ");
				format!("{} where {{ {bindings} }}", self.type_path(path))
			}
			BoundExpression::BoundList(bounds) => self
				.ast
				.list(bounds)
				.iter()
				.map(|&bound| self.bound(bound))
				.collect::<Vec<_>>()
				.join(" + "),
		}
	}

	/// A constant argument as written where only a constant can be (an
	/// array's length): a path without its `const`.
	fn constant(&self, constant: ConstId) -> String {
		match self.ast.constant(constant) {
			ConstArgument::Literal(literal) => {
				self.literal(literal, self.ast.const_span(constant))
			}
			ConstArgument::Path(segments) => self.type_path(segments),
			ConstArgument::QualifiedPath { root, segments } => {
				self.rooted(&self.qualified_root(root), segments, "")
			}
			ConstArgument::Grouped { inner, segments } => {
				self.rooted(&format!("<{}>", self.ty(inner)), segments, "")
			}
			ConstArgument::Infer => "_".to_string(),
		}
	}

	/// A type argument; a constant named by a path is marked `const`, which
	/// is what tells it from a type.
	fn type_argument(&self, argument: TypeArgument) -> String {
		match argument {
			TypeArgument::Type(ty) => self.ty(ty),
			TypeArgument::Const(constant) => {
				match self.ast.constant(constant) {
					ConstArgument::Path(_) => {
						format!("const {}", self.constant(constant))
					}
					_ => self.constant(constant),
				}
			}
		}
	}

	/// `<Type as Trait>`.
	fn qualified_root(&self, root: QualifiedRootId) -> String {
		let root = self.ast.qualified_root(root);
		format!(
			"<{} as {}>",
			self.ty(root.self_type),
			self.type_path(root.trait_path)
		)
	}

	/// A bracketed root and the segments after it.
	fn rooted(
		&self,
		root: &str,
		segments: List<PathSegment>,
		turbofish: &str,
	) -> String {
		let mut path = root.to_string();
		for segment in self.ast.list(segments) {
			path.push_str("::");
			path.push_str(&self.segment(segment, turbofish));
		}
		path
	}

	/// A path in a type, its arguments in bare `<..>`.
	fn type_path(&self, segments: List<PathSegment>) -> String {
		self.path(self.ast.list(segments), "")
	}

	/// The segments joined by `::`, each with its arguments after
	/// `turbofish` (`::` in a value, nothing in a type).
	fn path(&self, segments: &[PathSegment], turbofish: &str) -> String {
		segments
			.iter()
			.map(|segment| self.segment(segment, turbofish))
			.collect::<Vec<_>>()
			.join("::")
	}

	fn segment(&self, segment: &PathSegment, turbofish: &str) -> String {
		let name = self.name(segment.ident.inner);
		let arguments = self.ast.list(segment.type_args);
		if arguments.is_empty() {
			return name.to_string();
		}
		let arguments = arguments
			.iter()
			.map(|&argument| self.type_argument(argument))
			.collect::<Vec<_>>()
			.join(", ");
		format!("{name}{turbofish}<{arguments}>")
	}
}
