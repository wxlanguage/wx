//! Type-directed pattern completion, using checked types and prospective
//! positional insertion layouts. Explicit `const` uses the constant provider.

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{
	CompletionItem, CompletionResponse, InsertTextFormat,
};
use wx_compiler::ast::{self, AST, Destructure, Pattern, PatternElement};
use wx_compiler::diagnostics::{SourceSpan, TextOffset, TextSpan};
use wx_compiler::symbols::StringInterner;
use wx_compiler::tir::{
	BodyOwner, ConstIdx, DeclKind, Definition, FieldIdx, FieldListShape,
	FieldOwner, ItemLoc, NameUse, Operand, Reference, Semantics, Site, Type,
	TypeIndex, TypeList, positional_pattern_gap,
};
use wx_compiler::vfs::FileId;

use super::{Insert, after_name, item};
use crate::{query, snapshot::Snapshot};

pub(crate) struct PatternSite {
	pub target: PatternTarget,
	pub prefix: Option<TextSpan>,
	/// What the written position allows, before its ancestors narrow it.
	pub forms: PatternForms,
	/// Destructures crossed by cursor discovery, used only to narrow `forms`.
	pub ancestors: Vec<ast::PatId>,
}

/// Which forms a position permits, independently of its expected type.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(crate) enum PatternForms {
	/// A match arm: destructuring and tests of variants or constants.
	Tests,
	/// A `local`, or what an enum's representation holds: destructuring
	/// only, since a test cannot fail to match there.
	Bindings,
}

/// A struct or an enum written as the destructuring of its fields. An
/// existing delimiter or path continuation is never duplicated.
fn constructor_item(
	snapshot: &Snapshot,
	name: SymbolU32,
	loc: ItemLoc,
	suffix: &str,
	snippets: bool,
	label_details: bool,
) -> CompletionItem {
	let fields = match snapshot.sema.declaration_kind(loc) {
		DeclKind::Struct(index) => {
			snapshot.sema.decls.structs[usize::from(index)].fields
		}
		DeclKind::Enum(index) => {
			snapshot.sema.decls.enums[usize::from(index)].fields
		}
		_ => unreachable!("only a struct or an enum is a constructor"),
	};
	let (open, close) = if snapshot.sema.decls.fields.is_fully_named(fields) {
		('{', '}')
	} else {
		('(', ')')
	};
	let mut item = item(
		snapshot,
		name,
		Definition::Item(loc),
		Insert::Name,
		None,
		label_details,
	);
	let name = snapshot
		.strings
		.resolve(name)
		.expect("a listed name is interned");
	item.label = name.to_owned();
	item.filter_text = Some(name.to_owned());
	if suffix.starts_with(['{', '(']) || suffix.starts_with("::") {
		item.insert_text = Some(name.to_owned());
	} else if snippets {
		item.insert_text = Some(format!("{name}{open} ${{1:..}} {close}"));
		item.insert_text_format = Some(InsertTextFormat::SNIPPET);
	} else {
		item.insert_text = Some(format!("{name}{open} .. {close}"));
	}
	item
}

pub(super) fn complete(
	snapshot: &mut Snapshot,
	file: FileId,
	declaration: Definition,
	site: PatternSite,
	offset: TextOffset,
	snippets: bool,
	label_details: bool,
) -> Option<CompletionResponse> {
	let PatternSite {
		target,
		prefix,
		forms,
		ancestors,
	} = site;
	let owner = query::body_of(&snapshot.sema, declaration)?;
	let mut context = PatternContext {
		sema: &mut snapshot.sema,
		file,
		strings: &snapshot.strings,
		owner,
		ast: snapshot.compilation.ast(file),
	};
	let mut items = Vec::new();
	// A wildcard is valid without knowing a type, but not after a qualifier.
	if prefix.is_none() {
		items.push(CompletionItem {
			label: "_".into(),
			..Default::default()
		});
	}
	let forms = context.narrowed(forms, &ancestors);
	let Some(expected) = context.expected_type(target) else {
		return Some(CompletionResponse::Array(items));
	};
	let scope = snapshot.sema.body_scope(owner);
	let resolved_prefix = prefix.and_then(|prefix| {
		query::symbol_at(&snapshot.sema, file, prefix.start)
			.map(|(_, reference)| reference.definition())
	});
	let candidates = match (prefix, resolved_prefix) {
		(None, _) => snapshot.sema.names_at(owner, offset, NameUse::Pattern),
		(Some(_), Some(Definition::Item(loc))) => {
			snapshot.sema.names_in(scope, loc, NameUse::Pattern)
		}
		_ => return Some(CompletionResponse::Array(items)),
	};
	let source = &snapshot.compilation.files.get(file).ok()?.source;
	let suffix =
		after_name(source, snapshot.compilation.comments(file), offset);
	let constructor = match *snapshot.sema.types.resolve(expected) {
		Type::Enum { enum_index } if forms == PatternForms::Tests => {
			let enum_loc =
				snapshot.sema.decls.enums[usize::from(enum_index)].loc;
			// The qualifier may already name this enum; otherwise a visible
			// enum name in the selected namespace supplies the insertion path.
			let qualifier =
				if resolved_prefix == Some(Definition::Item(enum_loc)) {
					Some(String::new())
				} else {
					candidates
						.iter()
						.find(|(_, definition)| {
							*definition == Definition::Item(enum_loc)
						})
						.map(|&(name, _)| {
							let name = snapshot
								.strings
								.resolve(name)
								.expect("a listed name is interned");
							format!("{name}::")
						})
				};
			if let Some(qualifier) = qualifier {
				let variants =
					snapshot.sema.names_in(scope, enum_loc, NameUse::Pattern);
				let range = &snapshot.sema.decls.enums[usize::from(enum_index)]
					.variants;
				for index in u32::from(range.start)..u32::from(range.end) {
					let constant = ConstIdx::new(index);
					let loc = snapshot.sema.decls.constants
						[usize::from(constant)]
					.loc;
					let Some(&(name, definition)) =
						variants.iter().find(|(_, definition)| {
							*definition == Definition::Item(loc)
						})
					else {
						continue;
					};
					let mut candidate = item(
						snapshot,
						name,
						definition,
						Insert::Name,
						None,
						label_details,
					);
					let name = snapshot
						.strings
						.resolve(name)
						.expect("a listed name is interned");
					candidate.filter_text = Some(name.to_owned());
					candidate.insert_text = Some(format!("{qualifier}{name}"));
					candidate.sort_text = Some(format!("{index:010}"));
					items.push(candidate);
				}
			}
			None
		}
		Type::Enum { enum_index } => {
			Some(snapshot.sema.decls.enums[usize::from(enum_index)].loc)
		}
		Type::Struct { struct_index, .. } => {
			Some(snapshot.sema.decls.structs[usize::from(struct_index)].loc)
		}
		_ => None,
	};
	if let Some(loc) = constructor {
		for (name, definition) in candidates {
			if definition == Definition::Item(loc) {
				items.push(constructor_item(
					snapshot,
					name,
					loc,
					suffix,
					snippets,
					label_details,
				));
			}
		}
	}
	Some(CompletionResponse::Array(items))
}

/// A written child to replace, or a new positional child to insert.
#[derive(Clone, Copy)]
pub(crate) enum PatternTarget {
	/// The subject's type, including when a match has no arms.
	MatchGap(ast::ExprId),
	Written(ast::PatId),
	/// `at` is an insertion boundary in the parent's written element list,
	/// including `..` entries, from zero through the list's length.
	Insert {
		parent: ast::PatId,
		at: usize,
	},
}

/// A request-local view of an instantiated field owner, not retained metadata.
#[derive(Clone, Copy)]
struct Fields {
	owner: FieldOwner,
	args: TypeList,
}

/// The prospective positional list and the child being inserted into it.
struct PositionalInsertion {
	written: usize,
	rest: Option<usize>,
	slot: usize,
}

impl PositionalInsertion {
	fn element(&self, count: usize) -> Option<usize> {
		let gap = positional_pattern_gap(self.written, self.rest, count)?;
		Some(if self.slot < gap.start {
			self.slot
		} else {
			self.slot + gap.len()
		})
	}
}

struct PatternContext<'a> {
	sema: &'a mut Semantics,
	file: FileId,
	strings: &'a StringInterner,
	ast: &'a AST,
	owner: BodyOwner,
}

impl PatternContext<'_> {
	/// Cursor discovery supplies these ancestors while locating the site.
	/// Only the forms narrow through them; child types come from checking.
	fn narrowed(
		&self,
		forms: PatternForms,
		ancestors: &[ast::PatId],
	) -> PatternForms {
		let Some(body) = self.sema.owner_body(self.owner) else {
			return forms;
		};
		for &pattern in ancestors {
			let Pattern::Destructure(
				Destructure::Struct { path, .. }
				| Destructure::NamedStruct { path, .. },
			) = self.ast.pattern(pattern)
			else {
				continue;
			};
			let Some(ty) = body.pattern_type_of(self.ast, pattern) else {
				continue;
			};
			let Type::Enum { enum_index } = *self.sema.types.resolve(ty) else {
				continue;
			};
			let Some(segment) = self.ast.list(path).last() else {
				continue;
			};
			let site =
				Site::Value(SourceSpan::new(self.file, segment.ident.span));
			if let Some(Reference::Item { item, .. }) =
				self.sema.resolutions.by_site.get(&site)
				&& self.sema.declaration_kind(*item)
					== DeclKind::Enum(enum_index)
			{
				return PatternForms::Bindings;
			}
		}
		forms
	}

	/// Read an existing checked type; only a prospective insertion needs
	/// structural calculation. IDs and `owner` must belong to this snapshot.
	fn expected_type(&mut self, target: PatternTarget) -> Option<TypeIndex> {
		let ast = self.ast;
		let body = self.sema.owner_body(self.owner)?;
		let ty = match target {
			PatternTarget::MatchGap(expression) => {
				let Operand::Value(value) = body.operand_of(ast, expression)?
				else {
					return None;
				};
				body.operand_ty(Operand::Value(body.match_scrutinee(value)?))
			}
			PatternTarget::Written(pattern) => {
				body.pattern_type_of(ast, pattern)?
			}
			PatternTarget::Insert { parent, .. } => {
				body.pattern_type_of(ast, parent)?
			}
		};
		let ty = self.normalize_type(ty)?;
		let ty = match target {
			PatternTarget::Insert { parent, at } => {
				let inserted = self.insertion_type(parent, at, ty)?;
				self.normalize_type(inserted)?
			}
			_ => ty,
		};
		Some(ty)
	}

	fn normalize_type(&mut self, ty: TypeIndex) -> Option<TypeIndex> {
		if self.sema.types.needs_context(ty) || ty == TypeIndex::ERROR {
			return None;
		}
		let ty = self.sema.normalize_in_body(self.strings, self.owner, ty)?;
		(!self.sema.types.needs_context(ty) && ty != TypeIndex::ERROR)
			.then_some(ty)
	}

	fn insertion_type(
		&mut self,
		parent: ast::PatId,
		at: usize,
		expected: TypeIndex,
	) -> Option<TypeIndex> {
		let (elements, fields) = match self.ast.pattern(parent) {
			Pattern::Destructure(Destructure::Tuple { elements }) => {
				(elements, None)
			}
			Pattern::Destructure(Destructure::Struct { path, elements }) => {
				(elements, Some(self.pattern_fields(path, expected)?))
			}
			_ => return None,
		};
		let insertion = positional_insertion(self.ast.list(elements), at)?;
		let Some(fields) = fields else {
			// A tuple of one is its element, even if expected is itself a tuple.
			return if insertion.written == 1 && insertion.rest.is_none() {
				Some(expected)
			} else {
				self.tuple_pattern_element(expected, &insertion)
			};
		};
		let count = fields.owner.fields(&self.sema.decls).len();
		let lone = match count {
			1 => Some(self.pattern_field_type(fields, 0)?),
			_ => None,
		};
		let lone_tuple_field = lone.is_some_and(|field| {
			matches!(self.sema.types.resolve(field), Type::Tuple { .. })
		});
		match FieldListShape::of(
			insertion.written,
			insertion.rest,
			lone_tuple_field,
		) {
			FieldListShape::Whole => {
				let types = (0..count)
					.map(|field| self.pattern_field_type(fields, field))
					.collect::<Option<Vec<_>>>()?;
				Some(self.sema.types.intern_tuple(&types))
			}
			FieldListShape::LoneTuple => {
				self.tuple_pattern_element(lone?, &insertion)
			}
			FieldListShape::PerField => {
				self.pattern_field_type(fields, insertion.element(count)?)
			}
		}
	}

	fn tuple_pattern_element(
		&self,
		ty: TypeIndex,
		insertion: &PositionalInsertion,
	) -> Option<TypeIndex> {
		let Type::Tuple { elements } = *self.sema.types.resolve(ty) else {
			return None;
		};
		let types = self.sema.types.list(elements);
		Some(types[insertion.element(types.len())?])
	}

	fn pattern_fields(
		&self,
		path: ast::List<ast::PathSegment>,
		expected: TypeIndex,
	) -> Option<Fields> {
		let path = self.ast.list(path);
		// Written generic arguments have no source-to-checked-type query yet.
		// Do not ignore a conflicting argument or recheck its syntax here.
		if path.iter().any(|segment| !segment.type_args.is_empty()) {
			return None;
		}
		let site =
			Site::Value(SourceSpan::new(self.file, path.last()?.ident.span));
		let Reference::Item { item, .. } =
			self.sema.resolutions.by_site.get(&site).copied()?
		else {
			return None;
		};
		let fields = match (
			self.sema.declaration_kind(item),
			*self.sema.types.resolve(expected),
		) {
			(
				DeclKind::Struct(written),
				Type::Struct {
					struct_index,
					type_args,
				},
			) if written == struct_index => Fields {
				owner: FieldOwner::Struct(written),
				args: type_args,
			},
			(DeclKind::Enum(written), Type::Enum { enum_index })
				if written == enum_index =>
			{
				let field_owner = FieldOwner::Enum(written);
				Fields {
					owner: field_owner,
					args: TypeList::EMPTY,
				}
			}
			_ => return None,
		};
		let scope = self.sema.body_scope(self.owner);
		if (0..fields.owner.fields(&self.sema.decls).len()).any(|field| {
			!self.sema.field_accessible(
				fields.owner,
				FieldIdx::new(field as u32),
				scope,
			)
		}) {
			return None;
		}
		Some(fields)
	}

	fn pattern_field_type(
		&mut self,
		fields: Fields,
		field: usize,
	) -> Option<TypeIndex> {
		let ty = match fields.owner {
			FieldOwner::Struct(index) => {
				let signature = &self.sema.structs[usize::from(index)];
				let ty = self.sema.types.list(signature.field_types)[field];
				let env = signature.type_params;
				let args = self.sema.types.list(fields.args).to_vec();
				self.sema.substitute_type(ty, env, &args)
			}
			FieldOwner::Enum(index) => self
				.sema
				.types
				.list(self.sema.enums[usize::from(index)].field_types)[field],
		};
		self.sema.normalize_in_body(self.strings, self.owner, ty)
	}
}

/// Interpret a prospective insertion without allocating a modified AST list.
fn positional_insertion(
	elements: &[PatternElement],
	insertion: usize,
) -> Option<PositionalInsertion> {
	if insertion > elements.len() {
		return None;
	}
	let mut written = 0;
	let mut rest = None;
	let mut target = None;
	for at in 0..=elements.len() {
		if insertion == at {
			target = Some(written);
			written += 1;
		}
		let Some(element) = elements.get(at) else {
			break;
		};
		match *element {
			PatternElement::Rest(_) => {
				if rest.replace(written).is_some() {
					return None;
				}
			}
			PatternElement::Pattern(_) => {
				written += 1;
			}
		}
	}
	Some(PositionalInsertion {
		written,
		rest,
		slot: target?,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use wx_compiler::diagnostics::{Diagnostics, TextSpan};
	use wx_compiler::symbols::Keyword;
	use wx_compiler::tir::FunctionIdx;
	use wx_compiler::vfs::{
		AbsolutePath, CompilationUnit, CompilationUnitBuilder,
		VirtualFileSource,
	};

	struct Case {
		source: String,
		strings: StringInterner,
		graph: CompilationUnit,
		sema: Semantics,
		file: FileId,
		owner: BodyOwner,
		expression: ast::ExprId,
	}

	impl Case {
		fn new(source: &str) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let root = builder
				.load_package(
					AbsolutePath::new("/main.wx"),
					&VirtualFileSource::new(std::collections::HashMap::from([
						(AbsolutePath::new("/main.wx"), source.to_string()),
					])),
				)
				.unwrap();
			let graph = builder.build(root);
			assert!(
				!graph.collect_diagnostics().has_errors(),
				"{:?}",
				graph.collect_diagnostics(),
			);
			let sema = wx_compiler::tir::check(&graph, &mut strings);
			let function = (0..sema.decls.functions.len())
				.map(|at| FunctionIdx::new(at as u32))
				.find(|&index| {
					let loc = sema.decls.functions[usize::from(index)].loc;
					strings.resolve(sema.decls.item(loc).name.inner)
						== Some("f")
				})
				.unwrap();
			let file = sema
				.decls
				.file_id(sema.decls.functions[usize::from(function)].loc);
			let expression = graph
				.ast(file)
				.exprs
				.kinds
				.iter()
				.position(|kind| matches!(kind, ast::Expression::Match { .. }))
				.map(|at| ast::ExprId(at as u32))
				.unwrap();
			Self {
				source: source.into(),
				strings,
				graph,
				sema,
				file,
				owner: BodyOwner::Function(function),
				expression,
			}
		}

		fn pattern(&self, written: &str) -> ast::PatId {
			let start = self.source.find(written).unwrap();
			let span =
				TextSpan::from(start as u32..(start + written.len()) as u32);
			fn find(
				ast: &AST,
				pattern: ast::PatId,
				span: TextSpan,
			) -> Option<ast::PatId> {
				if ast.pattern_span(pattern) == span {
					return Some(pattern);
				}
				match ast.pattern(pattern) {
					Pattern::Or(alternatives) => ast
						.list(alternatives)
						.iter()
						.find_map(|&child| find(ast, child, span)),
					Pattern::Destructure(
						Destructure::Tuple { elements }
						| Destructure::Struct { elements, .. },
					) => ast.list(elements).iter().find_map(|element| {
						match element {
							PatternElement::Pattern(child) => {
								find(ast, *child, span)
							}
							_ => None,
						}
					}),
					Pattern::Destructure(Destructure::NamedStruct {
						fields,
						..
					}) => ast.list(fields).iter().find_map(|item| match item {
						ast::PatternFieldItem::Field(field) => field
							.pattern
							.and_then(|child| find(ast, child, span)),
						_ => None,
					}),
					_ => None,
				}
			}
			let ast = self.graph.ast(self.file);
			ast.exprs
				.kinds
				.iter()
				.find_map(|expression| {
					let ast::Expression::Match { arms, .. } = expression else {
						return None;
					};
					ast.list(*arms)
						.iter()
						.find_map(|arm| find(ast, arm.pattern, span))
				})
				.unwrap_or_else(|| panic!("no pattern `{written}`"))
		}

		fn query(&mut self, target: PatternTarget) -> Option<TypeIndex> {
			let diagnostics = self.sema.diagnostics().len();
			let resolutions = self.sema.resolutions.by_site.len();
			let answer = PatternContext {
				sema: &mut self.sema,
				file: self.file,
				strings: &self.strings,
				owner: self.owner,
				ast: self.graph.ast(self.file),
			}
			.expected_type(target);
			assert_eq!(self.sema.diagnostics().len(), diagnostics);
			assert_eq!(self.sema.resolutions.by_site.len(), resolutions);
			answer
		}

		fn expect(&mut self, target: PatternTarget, ty: &str) {
			let answer = self.query(target).expect("known expectation");
			assert_eq!(
				self.sema.type_formatter(&self.strings).display_type(answer),
				ty
			);
		}

		fn expect_pattern(&mut self, written: &str, ty: &str) {
			let pattern = self.pattern(written);
			self.expect(PatternTarget::Written(pattern), ty);
		}
	}

	#[test]
	fn empty_match_uses_checked_subject_not_the_match_result() {
		let mut case = Case::new("func f(value: Bool) { match (value) {} }");
		case.expect(PatternTarget::MatchGap(case.expression), "Bool");
	}

	#[test]
	fn grouped_ascribed_and_place_subjects_use_checked_types() {
		for subject in ["((value))", "(value: Bool)", "pointer.*"] {
			let mut case = Case::new(&format!(
				"memory heap: Memory32;
				 func f(value: Bool, pointer: heap::&Bool) {{
					match ({subject}) {{ target => {{}} }}
				 }}"
			));
			case.expect_pattern("target", "Bool");
		}
	}

	#[test]
	fn nested_named_fields_substitute_generic_arguments_and_aliases() {
		let mut case = Case::new(
			"struct Holder<T>(value: T);
			 struct Packet(item: Holder<Bool>);
			 use Holder as Alias;
			 func f(packet: Packet) {
				match (packet) { Packet{ item: Alias{ value: target } } => {} }
			 }",
		);
		case.expect_pattern("target", "Bool");
		assert!(!case.sema.diagnostics().has_errors());
	}

	#[test]
	fn tuples_and_alternatives_preserve_their_expected_types() {
		let mut case = Case::new(
			"func f(value: (u32, Bool)) {
				match (value) { (number, (target)) | (number, target) => {} }
			 }",
		);
		// The first target is wrapped in a transparent one-element tuple.
		case.expect_pattern("target", "Bool");
		case.expect_pattern("(target)", "Bool");
	}

	#[test]
	fn positional_fields_and_whole_field_tuple_have_distinct_types() {
		let mut case = Case::new(
			"struct Pair(a: u32, b: Bool);
			 func f(value: Pair) {
				match (value) { Pair(whole) => {}, Pair(first, second) => {} }
			 }",
		);
		case.expect_pattern("whole", "(u32, Bool)");
		case.expect_pattern("first", "u32");
		case.expect_pattern("second", "Bool");
	}

	#[test]
	fn one_tuple_valued_field_flattens_for_multiple_children() {
		let mut case = Case::new(
			"struct Wrapper(value: (u32, Bool));
			 func f(value: Wrapper) {
				match (value) { Wrapper(whole) => {}, Wrapper(first, second) => {} }
			 }",
		);
		case.expect_pattern("whole", "(u32, Bool)");
		case.expect_pattern("first", "u32");
		case.expect_pattern("second", "Bool");
	}

	#[test]
	fn rest_maps_prefix_and_suffix_to_their_declared_fields() {
		let mut case = Case::new(
			"struct Three(a: u8, b: u32, c: Bool);
			 func f(value: Three) {
				match (value) { Three(first, .., last) => {} }
			 }",
		);
		case.expect_pattern("first", "u8");
		case.expect_pattern("last", "Bool");
	}

	#[test]
	fn insertion_uses_the_prospective_shape_not_the_existing_child_type() {
		let mut case = Case::new(
			"struct Pair(a: u32, b: Bool);
			 func f(value: Pair) { match (value) { Pair(whole) => {} } }",
		);
		let parent = case.pattern("Pair(whole)");
		case.expect_pattern("whole", "(u32, Bool)");
		case.expect(PatternTarget::Insert { parent, at: 0 }, "u32");
		case.expect(PatternTarget::Insert { parent, at: 1 }, "Bool");
		assert!(
			case.query(PatternTarget::Insert { parent, at: 2 })
				.is_none()
		);

		let mut case = Case::new(
			"struct Pair(a: u32, b: Bool);
			 func f(value: Pair) { match (value) { Pair() => {} } }",
		);
		let parent = case.pattern("Pair()");
		case.expect(PatternTarget::Insert { parent, at: 0 }, "(u32, Bool)");
	}

	#[test]
	fn insertion_around_rest_respects_its_written_boundary() {
		let mut case = Case::new(
			"struct Three(a: u8, b: u32, c: Bool);
			 func f(value: Three) { match (value) { Three(..) => {} } }",
		);
		let parent = case.pattern("Three(..)");
		case.expect(PatternTarget::Insert { parent, at: 0 }, "u8");
		case.expect(PatternTarget::Insert { parent, at: 1 }, "Bool");
	}

	#[test]
	fn insertion_does_not_guess_a_field_when_the_prospective_count_is_wrong() {
		let mut case = Case::new(
			"struct Three(a: u8, b: u32, c: Bool);
			 func f(value: Three) { match (value) { Three(first) => {} } }",
		);
		let parent = case.pattern("Three(first)");
		for at in [0, 1] {
			assert!(case.query(PatternTarget::Insert { parent, at }).is_none());
		}
	}

	#[test]
	fn enum_repr_children_have_checked_types() {
		let mut case = Case::new(
			"enum Flag(pub value: u8) { Off = 0, On = 1 }
			 func f(value: Flag) { match (value) { Flag((target)) => {} } }",
		);
		let target = case.pattern("target");
		case.expect(PatternTarget::Written(target), "u8");
		let parent = case.pattern("Flag((target))");
		let context = PatternContext {
			sema: &mut case.sema,
			file: case.file,
			strings: &case.strings,
			owner: case.owner,
			ast: case.graph.ast(case.file),
		};
		assert_eq!(
			context.narrowed(PatternForms::Tests, &[parent]),
			PatternForms::Bindings
		);
	}

	#[test]
	fn bad_counts_do_not_invent_child_expectations() {
		let mut case = Case::new(
			"struct Three(a: u8, b: u32, c: Bool);
			 func f(value: Three) { match (value) { Three(first, second) => {} } }",
		);
		assert!(case.sema.diagnostics().has_errors());
		for written in ["first", "second"] {
			let pattern = case.pattern(written);
			assert!(case.query(PatternTarget::Written(pattern)).is_none());
		}

		let mut case = Case::new(
			"struct Pair(a: u32, b: Bool);
			 func f(value: Pair) { match (value) { Pair(a, b, target) => {} } }",
		);
		let target = case.pattern("target");
		assert!(case.query(PatternTarget::Written(target)).is_none());
	}

	#[test]
	fn unresolved_and_incompatible_owners_are_not_guessed() {
		for constructor in ["Unknown", "Other", "Holder::<u32>"] {
			let mut case = Case::new(&format!(
				"struct Holder<T>(value: T);
				 struct Other(value: u32);
				 func f(value: Holder<Bool>) {{
					match (value) {{ {constructor}{{ value: target }} => {{}} }}
				 }}"
			));
			let target = case.pattern("target");
			assert!(
				case.query(PatternTarget::Written(target)).is_none(),
				"{constructor}"
			);
		}
	}

	#[test]
	fn checked_written_generic_arguments_supply_child_types() {
		let mut case = Case::new(
			"struct Holder<T>(value: T);
			 func f(value: Holder<Bool>) {
				match (value) { Holder::<Bool>{ value: target } => {} }
			 }",
		);
		case.expect_pattern("target", "Bool");
	}

	#[test]
	fn wrong_body_or_unrelated_target_has_no_answer() {
		let mut case = Case::new(
			"func f(value: Bool) { match (value) { target => {} } }
			 func g(value: u32) { match (value) { other => {} } }",
		);
		let other = case.pattern("other");
		assert!(case.query(PatternTarget::Written(other)).is_none());
		let function = (0..case.sema.decls.functions.len())
			.map(|at| FunctionIdx::new(at as u32))
			.find(|&index| {
				let loc = case.sema.decls.functions[usize::from(index)].loc;
				case.strings.resolve(case.sema.decls.item(loc).name.inner)
					== Some("g")
			})
			.unwrap();
		case.owner = BodyOwner::Function(function);
		assert!(
			case.query(PatternTarget::MatchGap(case.expression))
				.is_none()
		);
	}

	#[test]
	fn written_pattern_lookup_needs_only_its_owning_body() {
		let mut case = Case::new(
			"func f(value: Bool, number: u32) {
				match (value) { first => {} };
				match (number) { second => {} }
			 }",
		);
		// The test fixture stores the first match, but a written pattern's
		// type is obtained directly from its owning body, not that match.
		case.expect_pattern("second", "u32");
	}

	#[test]
	fn repeated_queries_do_not_recheck_or_accumulate_diagnostics() {
		let mut case = Case::new(
			"struct Holder<T>(value: T);
			 func f(value: Holder<Bool>) {
				match (value) { Holder{ value: target } => {} }
			 }",
		);
		let target = case.pattern("target");
		let first = case.query(PatternTarget::Written(target));
		assert!(first.is_some());
		for _ in 0..10 {
			assert_eq!(case.query(PatternTarget::Written(target)), first);
		}
	}
}
