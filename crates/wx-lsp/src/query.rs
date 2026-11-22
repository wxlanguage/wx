//! Questions requests ask of a checked package, answered from what checking
//! left behind: the name resolution table (`Semantics::resolutions`, ordered
//! here as [`References`]), the declarations and the bodies. None of them is
//! the checker's own: each reads what it decided and never decides anything
//! again.

use std::collections::BTreeMap;

use string_interner::symbol::SymbolU32;
use wx_compiler::diagnostics::{SourceSpan, TextOffset, TextSpan};
use wx_compiler::tir::{
	BodyOwner, ConstIdx, DeclKind, Definition, EnumIdx, FieldIdx, FieldOwner,
	FunctionIdx, GlobalIdx, InherentImplIdx, LocalIdx, MemberKind, ParamIdx,
	Reference, Semantics, Site, StructIdx, TargetIdx, TraitImplIdx,
};
use wx_compiler::vfs::FileId;

/// Every resolved name, by where it is written: by file, then position, then
/// role, so that the entries of one written name are adjacent and "the name
/// at this offset" is a range lookup.
pub(crate) type References = BTreeMap<Site, Reference>;

/// The checker's resolution table, ordered. A name it resolved twice has the
/// same meaning both times, so either entry is the one kept.
pub(crate) fn references(sema: &Semantics) -> References {
	sema.resolutions.iter().collect()
}

/// Which of the entries at one name is the one it means where it is used:
/// the value, then the type, then the label.
fn priority(site: Site) -> u8 {
	match site {
		Site::Value(_) => 2,
		Site::Type(_) => 1,
		Site::Label(_) => 0,
	}
}

/// What the name written at `offset` in `file` resolved to, with the span of
/// the name. `None` when no resolved name is written there.
///
/// Names do not nest, so the entry is the last one starting at or before
/// `offset`. One written name can hold up to three entries (the roles of one
/// site: a `use` leaf is a type and a value, a shorthand argument is a label
/// and a value); `priority` picks the one the name means where it is used.
pub(crate) fn symbol_at(
	references: &References,
	file: FileId,
	offset: TextOffset,
) -> Option<(SourceSpan, Reference)> {
	let probe = Site::Label(SourceSpan::new(
		file,
		TextSpan {
			start: offset,
			end: TextOffset::from(u32::MAX),
		},
	));
	let mut found: Option<(SourceSpan, Site, Reference)> = None;
	for (&site, &reference) in references.range(..=probe).rev() {
		let span = site.span();
		if span.file_id != file || span.span.end < offset {
			break;
		}
		if found.is_some_and(|(found, ..)| found != span) {
			break;
		}
		// A zero-width synthetic span never covers a cursor.
		if span.span.start == span.span.end {
			continue;
		}
		if found.is_none_or(|(_, kept, _)| priority(site) > priority(kept)) {
			found = Some((span, site, reference));
		}
	}
	found.map(|(span, _, reference)| (span, reference))
}

/// Every resolved name written in `file`, in source order, one per name:
/// where a name holds several entries, the one `symbol_at` would answer.
/// Zero-width synthetic spans are skipped, since nothing is written there.
pub(crate) fn resolutions_in(
	references: &References,
	file: FileId,
) -> impl Iterator<Item = (SourceSpan, Reference)> + '_ {
	// The least site of `file`: the empty span at its start, first role.
	let start =
		Site::Type(SourceSpan::new(file, TextSpan::empty_at(TextOffset::ZERO)));
	let mut entries = references
		.range(start..)
		.take_while(move |(site, _)| site.span().file_id == file)
		.filter(|(site, _)| {
			let span = site.span().span;
			span.start != span.end
		})
		.peekable();
	std::iter::from_fn(move || {
		let (&site, &reference) = entries.next()?;
		let mut found = (site, reference);
		while let Some((&next, &reference)) =
			entries.next_if(|(next, _)| next.span() == site.span())
		{
			if priority(next) > priority(found.0) {
				found = (next, reference);
			}
		}
		Some((found.0.span(), found.1))
	})
}

/// Every resolved meaning of the name written at exactly `span`: one per
/// role it plays there (a shorthand argument is a label and a value).
pub(crate) fn references_at(
	references: &References,
	span: SourceSpan,
) -> impl Iterator<Item = Reference> + '_ {
	references
		.range(Site::Type(span)..=Site::Label(span))
		.map(|(_, &reference)| reference)
}

/// Every resolved name referring to `definition`, in source order and
/// without duplicate spans. Declarations are not references; callers may
/// include `Semantics::definition_span` separately. All roles at a site
/// participate: a shorthand can refer to both a parameter/field and its
/// supplied value.
pub(crate) fn references_to(
	sema: &Semantics,
	references: &References,
	definition: Definition,
) -> Vec<SourceSpan> {
	let definition = reference_identity(sema, definition);
	let mut found = Vec::new();
	for (site, reference) in references {
		let span = site.span();
		if span.span.start != span.span.end
			&& reference_identity(sema, reference.definition()) == definition
			&& found.last() != Some(&span)
		{
			found.push(span);
		}
	}
	found
}

/// Whether `a` and `b` name the same declaration, as `references_to`
/// compares them: a parameter and the local it binds, a trait member reached
/// as an item and through a type, are one.
pub(crate) fn same_definition(
	sema: &Semantics,
	a: Definition,
	b: Definition,
) -> bool {
	reference_identity(sema, a) == reference_identity(sema, b)
}

/// Different ways of naming the same declaration, not declarations that
/// merely navigate to the same span (a trait and its `Self`, for example).
fn reference_identity(sema: &Semantics, definition: Definition) -> Definition {
	match definition {
		Definition::Item(key) => match sema.declaration_kind(key) {
			DeclKind::Function(index) => {
				Definition::Member(MemberKind::Function(index))
			}
			DeclKind::Const(index) | DeclKind::EnumVariant(index) => {
				Definition::Member(MemberKind::Constant(index))
			}
			DeclKind::AssocType(index) => {
				Definition::Member(MemberKind::AssociatedType(index))
			}
			_ => definition,
		},
		Definition::Member(MemberKind::Method(index)) => {
			Definition::Member(MemberKind::Function(index))
		}
		Definition::Parameter {
			function,
			parameter,
		} => {
			let owner = BodyOwner::Function(function);
			sema.owner_body(owner)
				.and_then(|body| body.params().get(usize::from(parameter)))
				.copied()
				.flatten()
				.map_or(definition, |local| Definition::Local { owner, local })
		}
		_ => definition,
	}
}

/// Whether the name `name` written at `span` is an entry of the export block
/// with no `as "..."`, so its Wasm export name is its own name.
pub(crate) fn exported_under_own_name(
	sema: &Semantics,
	name: SymbolU32,
	span: SourceSpan,
) -> bool {
	// An entry's external span is its name's own when it has no alias, and
	// the quoted string's when it has one.
	sema.decls
		.exports
		.get(&name)
		.is_some_and(|entry| entry.external_span == span)
}

/// Where go-to-definition leads for `definition`: where it is declared,
/// except a module in a file of its own, which leads to the start of that
/// file, its contents.
pub(crate) fn definition_target(
	sema: &Semantics,
	definition: Definition,
) -> Option<SourceSpan> {
	if let Definition::Item(key) = definition
		&& let DeclKind::Module(index) = sema.declaration_kind(key)
	{
		let module = &sema.decls.modules[usize::from(index)];
		if module.own_file != sema.decls.file_id(module.loc) {
			return Some(SourceSpan::new(
				module.own_file,
				TextSpan::empty_at(TextOffset::ZERO),
			));
		}
	}
	sema.definition_span(definition)
}

/// Whether the compiler provides `definition`, with no wx definition behind
/// it: a function core leaves to the compiler (a package function of core's,
/// as `transmute` or an intrinsic, and `Slice`'s bodiless `len` and
/// `as_ref`), a primitive type or a literal kind. A function core writes a
/// body for is an ordinary function, even when that body calls one of these.
pub(crate) fn is_compiler_provided(
	sema: &Semantics,
	definition: Definition,
) -> bool {
	let decls = &sema.decls;
	let function = match definition {
		Definition::Item(key) => match sema.declaration_kind(key) {
			DeclKind::Function(function) => function,
			DeclKind::TypeAlias(alias) => {
				return decls.intrinsics.is_builtin_type(alias);
			}
			_ => return false,
		},
		Definition::Member(
			MemberKind::Function(function) | MemberKind::Method(function),
		) => function,
		_ => return false,
	};
	decls.is_core_package_function(function)
		|| [decls.intrinsics.slice_len, decls.intrinsics.slice_as_ref]
			.contains(&Some(function))
}

/// Every declared name that has a written name, with where it is written. A
/// declaration is its row, a member's included; a generated one's name span
/// is empty (a package's own entry, a typeset's trait, a generated impl's
/// associated types), so it is skipped. Where two still share a span (a
/// trait and its `Self`), the item wins.
pub(crate) fn definitions(
	sema: &Semantics,
) -> BTreeMap<SourceSpan, Definition> {
	let decls = &sema.decls;
	let mut found = BTreeMap::new();
	let mut add = |definition: Definition| {
		if let Some(span) = sema.definition_span(definition)
			&& span.span.start != span.span.end
		{
			found.insert(span, definition);
		}
	};
	let structs = decls.structs.iter().enumerate().map(|(index, decl)| {
		(
			FieldOwner::Struct(StructIdx::new(index as u32)),
			decl.fields,
		)
	});
	let enums = decls.enums.iter().enumerate().map(|(index, decl)| {
		(FieldOwner::Enum(EnumIdx::new(index as u32)), decl.fields)
	});
	for (owner, fields) in structs.chain(enums) {
		for field in 0..fields.len() {
			add(Definition::Field {
				owner,
				field: FieldIdx::new(field as u32),
			});
		}
	}
	for env in sema.generic_envs.frames() {
		for index in 0..sema.generic_envs.param_names(env).len() {
			add(Definition::TypeParam {
				env,
				index: index as u32,
			});
		}
	}
	for index in 0..decls.functions.len() {
		let function = FunctionIdx::new(index as u32);
		let owner = BodyOwner::Function(function);
		// A parameter of a function with a body is a local of it; the others
		// are known by the declaration alone.
		if sema.owner_body(owner).is_none() {
			for parameter in 0..decls.functions[index].params.len() {
				add(Definition::Parameter {
					function,
					parameter: ParamIdx::new(parameter as u32),
				});
			}
		}
		if sema.owner_body(owner).is_some() {
			add(Definition::FunctionBody(function));
		}
		add_body_definitions(sema, owner, &mut add);
	}
	for index in 0..decls.constants.len() {
		let owner = BodyOwner::Const(ConstIdx::new(index as u32));
		add_body_definitions(sema, owner, &mut add);
	}
	for index in 0..decls.globals.len() {
		let owner = BodyOwner::Global(GlobalIdx::new(index as u32));
		add_body_definitions(sema, owner, &mut add);
	}
	for key in decls.namespaces.keys() {
		add(Definition::Item(key));
	}
	found
}

fn add_body_definitions(
	sema: &Semantics,
	owner: BodyOwner,
	add: &mut impl FnMut(Definition),
) {
	let Some(body) = sema.owner_body(owner) else {
		return;
	};
	for index in 0..body.locals().len() {
		add(Definition::Local {
			owner,
			local: LocalIdx::new(index as u32),
		});
	}
	for (index, jump_target) in body.targets().iter().enumerate() {
		let target = TargetIdx::new(index as u32);
		if jump_target.label.is_some() {
			add(Definition::Label { owner, target });
		}
		add(Definition::JumpTarget { owner, target });
	}
}

/// The body `declaration` owns: a function's block, a constant's or a
/// global's initializer (an enum variant's value is a constant's).
pub(crate) fn body_of(
	sema: &Semantics,
	declaration: Definition,
) -> Option<BodyOwner> {
	let Definition::Item(loc) = declaration else {
		return None;
	};
	let owner = match sema.declaration_kind(loc) {
		DeclKind::Function(index) => BodyOwner::Function(index),
		DeclKind::Const(index) | DeclKind::EnumVariant(index) => {
			BodyOwner::Const(index)
		}
		DeclKind::Global(index) => BodyOwner::Global(index),
		_ => return None,
	};
	sema.owner_body(owner).is_some().then_some(owner)
}

/// Every impl, by the span of its target's path (`ast::Path::span`, what
/// `Self` there names), the one span an impl keeps; a generated impl (a
/// function's `Call`) by its generator's.
pub(crate) fn impls(
	sema: &Semantics,
) -> impl Iterator<Item = (SourceSpan, Definition)> + '_ {
	let inherent = (0..sema.inherent_impls.len()).map(|index| {
		Definition::InherentImplTarget(InherentImplIdx::new(index as u32))
	});
	let traits = (0..sema.trait_impls.len()).map(|index| {
		Definition::TraitImplTarget(TraitImplIdx::new(index as u32))
	});
	inherent.chain(traits).filter_map(|definition| {
		Some((sema.definition_span(definition)?, definition))
	})
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;

	use indoc::indoc;
	use wx_compiler::diagnostics::Diagnostics as _;
	use wx_compiler::symbols::{Keyword, StringInterner};
	use wx_compiler::tir::{self, ItemLoc, Route};
	use wx_compiler::vfs::{self, AbsolutePath, VirtualFileSource};

	use super::*;

	struct Analysis<'s> {
		source: &'s str,
		file: FileId,
		strings: StringInterner,
		sema: Semantics,
		references: References,
	}

	impl<'s> Analysis<'s> {
		fn new(source: &'s str) -> Self {
			let mut strings = Keyword::create_interner();
			let mut builder = vfs::CompilationUnitBuilder::new(&mut strings);
			builder.load_core();
			let path = AbsolutePath::new("/main.wx");
			let root = builder
				.load_package(
					path.clone(),
					&VirtualFileSource::new(HashMap::from([(
						path.clone(),
						source.to_string(),
					)])),
				)
				.unwrap();
			let compilation = builder.build(root);
			let parse_diagnostics = compilation.collect_diagnostics();
			assert!(!parse_diagnostics.has_errors(), "{parse_diagnostics:?}");
			let sema = tir::check(&compilation, &mut strings);
			// Core's entry is `/main.wx` as well, in its own package.
			let file = compilation
				.packages
				.iter()
				.find(|package| package.id == root)
				.and_then(|package| {
					package
						.modules
						.iter()
						.find(|module| module.file_path == path)
				})
				.unwrap()
				.file_id;
			Self {
				source,
				file,
				strings,
				references: references(&sema),
				sema,
			}
		}

		fn clean(source: &'s str) -> Self {
			let analysis = Self::new(source);
			assert!(
				!analysis.sema.diagnostics().has_errors(),
				"{:?}",
				analysis.sema.diagnostics().errors().collect::<Vec<_>>()
			);
			analysis
		}

		fn span(&self, context: &str, name: &str) -> SourceSpan {
			let start = self.source.find(context).unwrap()
				+ context.find(name).unwrap();
			SourceSpan::new(
				self.file,
				TextSpan::from(start as u32..(start + name.len()) as u32),
			)
		}

		fn get(&self, site: Site) -> Option<Reference> {
			self.references.get(&site).copied()
		}

		fn ty(&self, context: &str, name: &str) -> Reference {
			self.get(Site::Type(self.span(context, name)))
				.unwrap_or_else(|| {
					panic!("type `{name}` in `{context}` was not recorded")
				})
		}

		fn value(&self, context: &str, name: &str) -> Reference {
			self.get(Site::Value(self.span(context, name)))
				.unwrap_or_else(|| {
					panic!("`{name}` in `{context}` was not recorded")
				})
		}

		fn label(&self, context: &str, name: &str) -> Reference {
			self.get(Site::Label(self.span(context, name)))
				.unwrap_or_else(|| {
					panic!("label `{name}` in `{context}` was not recorded")
				})
		}

		/// The one declaration named `name` that `is` accepts the kind of.
		fn item(&self, name: &str, is: impl Fn(DeclKind) -> bool) -> ItemLoc {
			let symbol = self.strings.get(name).unwrap();
			let decls = &self.sema.decls;
			let mut found = decls.namespaces.keys().filter(|&key| {
				let item = decls.item(key);
				item.name.inner == symbol && is(item.kind)
			});
			let item = found.next().unwrap_or_else(|| panic!("no `{name}`"));
			assert!(found.next().is_none(), "`{name}` is ambiguous");
			item
		}

		fn function(&self, name: &str) -> FunctionIdx {
			let loc =
				self.item(name, |kind| matches!(kind, DeclKind::Function(_)));
			let DeclKind::Function(index) = self.sema.declaration_kind(loc)
			else {
				unreachable!()
			};
			index
		}

		/// What go-to-definition from `offset` reaches.
		fn definition_at(&self, offset: TextOffset) -> Option<SourceSpan> {
			let (_, reference) =
				symbol_at(&self.references, self.file, offset)?;
			definition_target(&self.sema, reference.definition())
		}
	}

	#[test]
	fn references_join_parameter_labels_and_body_locals_and_deduplicate_roles()
	{
		let a = Analysis::clean(indoc! {"
			func take(value: u32) -> u32 {
				_ = take{ value: 1 };
				_ = take{ value };
				value
			}
		"});
		let local = a.value("\n\tvalue\n", "value").definition();
		let parameter = a.label("{ value: 1", "value").definition();
		let expected = [
			a.span("{ value: 1", "value"),
			a.span("{ value }", "value"),
			a.span("\n\tvalue\n", "value"),
		];
		assert_ne!(local, parameter);
		assert_eq!(references_to(&a.sema, &a.references, local), expected);
		assert_eq!(references_to(&a.sema, &a.references, parameter), expected);
	}

	#[test]
	fn references_include_both_constructor_tiers_and_import_routes() {
		let a = Analysis::clean(indoc! {"
			mod m { pub struct S(); }
			use m::S as Alias;
			func f(s: Alias) -> m::S { Alias() }
		"});
		let ty = a.ty("s: Alias", "Alias").definition();
		let value = a.value("{ Alias()", "Alias").definition();
		let expected = [
			a.span("use m::S", "S"),
			a.span("s: Alias", "Alias"),
			a.span("-> m::S", "S"),
			a.span("{ Alias()", "Alias"),
		];
		assert_eq!(references_to(&a.sema, &a.references, ty), expected);
		assert_eq!(references_to(&a.sema, &a.references, value), expected);
	}

	#[test]
	fn references_preserve_owner_identity_across_reads_and_writes() {
		let a = Analysis::clean(indoc! {"
			func f() -> u32 {
				local mut x: u32 = 0;
				x = 1;
				x += 2;
				local _ = block { local x: u32 = 3; x };
				x
			}
			func g(x: u32) -> u32 { x }
		"});
		let definition = a.value("x = 1", "x").definition();
		assert_eq!(
			references_to(&a.sema, &a.references, definition),
			[
				a.span("x = 1", "x"),
				a.span("x += 2", "x"),
				a.span("\n\tx\n", "x"),
			]
		);
	}

	#[test]
	fn references_do_not_merge_a_trait_with_its_self_parameter() {
		let a = Analysis::clean(indoc! {"
			trait Tr: StackValue { func id(self: Self) -> Self { self } }
			func f<T: Tr>(x: T) -> T { x.id() }
		"});
		let tr = a.ty("T: Tr", "Tr").definition();
		let self_ty = a.ty("self: Self", "Self").definition();
		assert_eq!(a.sema.definition_span(tr), a.sema.definition_span(self_ty));
		assert_eq!(
			references_to(&a.sema, &a.references, tr),
			[a.span("T: Tr", "Tr")]
		);
		assert_eq!(references_to(&a.sema, &a.references, self_ty).len(), 2);
	}

	#[test]
	fn references_find_members_from_their_declarations() {
		let a = Analysis::clean(indoc! {"
			struct S();
			impl S {
				func id(self: Self) -> Self { self }
			}
			func f(s: S) -> S { S::id(s).id() }
		"});
		let definition = a.value("S::id", "id").definition();
		assert_eq!(
			references_to(&a.sema, &a.references, definition),
			[a.span("S::id", "id"), a.span(".id()", "id")]
		);
		let declared = definitions(&a.sema)[&a.span("func id", "id")];
		assert_eq!(
			references_to(&a.sema, &a.references, declared),
			references_to(&a.sema, &a.references, definition)
		);
	}

	#[test]
	fn references_find_labels_type_parameters_and_bodyless_parameters() {
		let a = Analysis::clean(indoc! {r#"
			import "host" as host { func take(value: u32); }
			func f<T: StackValue>(x: T) -> T {
				host::take{ value: 1 };
				loop :done { break :done; }
				x
			}
		"#});
		let declarations = definitions(&a.sema);
		for (reference, contexts, name) in [
			(a.label("value: 1", "value"), vec!["value: 1"], "value"),
			(a.label("break :done", "done"), vec!["break :done"], "done"),
			(a.ty("x: T", "T"), vec!["x: T", "-> T"], "T"),
		] {
			let definition = reference.definition();
			let span = a.sema.definition_span(definition).unwrap();
			let declared = declarations[&span];
			let expected: Vec<_> = contexts
				.into_iter()
				.map(|context| a.span(context, name))
				.collect();
			assert_eq!(
				references_to(&a.sema, &a.references, definition),
				expected
			);
			assert_eq!(
				references_to(&a.sema, &a.references, declared),
				expected
			);
		}
	}

	/// A source with labelled positions. `$[label]` is written right before a
	/// name and is removed from the text the compiler sees; the label stands
	/// for that name's position.
	struct Marked {
		source: String,
		marks: Vec<(&'static str, u32)>,
	}

	impl Marked {
		fn new(marked: &'static str) -> Self {
			let mut source = String::new();
			let mut marks = Vec::new();
			let mut rest = marked;
			while let Some(open) = rest.find("$[") {
				source.push_str(&rest[..open]);
				let after = &rest[open + "$[".len()..];
				let close = after.find(']').expect("an unclosed marker");
				marks.push((&after[..close], source.len() as u32));
				rest = &after[close + "]".len()..];
			}
			source.push_str(rest);
			Self { source, marks }
		}

		/// The span of the name the mark `label` is written before.
		fn name(&self, label: &str) -> TextSpan {
			let (_, start) = *self
				.marks
				.iter()
				.find(|(mark, _)| *mark == label)
				.unwrap_or_else(|| panic!("no mark `{label}`"));
			let length = self.source[start as usize..]
				.find(|c: char| !c.is_alphanumeric() && c != '_')
				.unwrap_or(self.source.len() - start as usize);
			TextSpan::from(start..start + length as u32)
		}

		/// Asserts that the cursor on the name marked `used` (at its start,
		/// inside it and at its end) goes to the name marked `declared`.
		#[track_caller]
		fn assert_definition(
			&self,
			analysis: &Analysis<'_>,
			used: &str,
			declared: &str,
		) {
			let used_span = self.name(used);
			let declared_span =
				SourceSpan::new(analysis.file, self.name(declared));
			for offset in [used_span.start, used_span.start + 1, used_span.end]
			{
				assert_eq!(
					analysis.definition_at(offset),
					Some(declared_span),
					"from `{used}` at offset {offset}"
				);
			}
		}
	}

	#[test]
	fn definition_at_reaches_items_locals_labels_parameters_and_fields() {
		let marked = Marked::new(indoc! {"
			struct $[Point]Point($[width]width: i32, height: i32);
			func $[make]make($[amount]amount: i32) -> i32 {
				local $[total]total = $[amount.read]amount;
				loop :$[done]done { break :$[done.break]done $[total.read]total }
			}
			func main() {
				local p = $[Point.call]Point{ $[width.label]width: 1, height: 2 };
				_ = $[make.call]make{ $[amount.label]amount: 3 };
				local q: $[Point.type]Point = p;
			}
		"});
		let analysis = Analysis::clean(&marked.source);
		for (used, declared) in [
			("Point.call", "Point"),
			("Point.type", "Point"),
			("make.call", "make"),
			("amount.read", "amount"),
			("amount.label", "amount"),
			("total.read", "total"),
			("done.break", "done"),
			("width.label", "width"),
		] {
			marked.assert_definition(&analysis, used, declared);
		}
	}

	#[test]
	fn definition_at_reaches_type_parameters_and_members() {
		let marked = Marked::new(indoc! {"
			struct $[Meters]Meters(value: u32);
			impl Meters { pub func $[zero]zero() -> Meters { Meters(0) } }
			func id<$[Elem]Elem: StackValue>(x: $[Elem.param]Elem) -> $[Elem.result]Elem { x }
			func main() { local m = $[Meters.path]Meters::$[zero.call]zero(); }
		"});
		let analysis = Analysis::clean(&marked.source);
		for (used, declared) in [
			("Elem.param", "Elem"),
			("Elem.result", "Elem"),
			("zero.call", "zero"),
			("Meters.path", "Meters"),
		] {
			marked.assert_definition(&analysis, used, declared);
		}
	}

	#[test]
	fn definition_at_is_none_away_from_a_resolved_name() {
		let source = "func f() { local x = 1; }";
		let analysis = Analysis::new(source);
		let keyword = TextOffset::from(source.find("local").unwrap() as u32);
		assert_eq!(analysis.definition_at(keyword), None);
		assert_eq!(
			analysis.definition_at(TextOffset::from(source.len() as u32 + 5)),
			None
		);
	}

	#[test]
	fn references_at_lists_every_role_of_one_name() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) {
				take{ x };
			}
		"});
		let found: Vec<_> =
			references_at(&a.references, a.span("{ x }", "x")).collect();
		// The parameter it labels, and the local it supplies.
		assert_eq!(found.len(), 2, "{found:?}");
		assert!(found.contains(&a.label("{ x }", "x")));
		assert!(found.contains(&a.value("{ x }", "x")));
		// A parameter named by a label is the local it binds.
		assert!(same_definition(
			&a.sema,
			a.label("{ x }", "x").definition(),
			Reference::Local {
				owner: BodyOwner::Function(a.function("take")),
				local: LocalIdx::new(0),
			}
			.definition(),
		));
	}

	#[test]
	fn an_export_entry_without_as_is_exported_under_its_own_name() {
		let a = Analysis::clean(indoc! {"
			func run() {}
			func tick() {}
			export { run, tick as \"step\" }
		"});
		let symbol = |name: &str| a.strings.get(name).unwrap();
		assert!(exported_under_own_name(
			&a.sema,
			symbol("run"),
			a.span("{ run,", "run")
		));
		// Exported under the alias, so not under its own name.
		assert!(!exported_under_own_name(
			&a.sema,
			symbol("tick"),
			a.span("tick as", "tick")
		));
		// The declaration is no export entry.
		assert!(!exported_under_own_name(
			&a.sema,
			symbol("run"),
			a.span("func run", "run")
		));
	}

	#[test]
	fn only_what_core_leaves_to_the_compiler_is_compiler_provided() {
		let a = Analysis::clean("func f() {}");
		let function = |name| {
			Definition::Item(
				a.item(name, |kind| matches!(kind, DeclKind::Function(_))),
			)
		};
		let ty = |name| {
			Definition::Item(a.item(name, |kind| {
				matches!(kind, DeclKind::TypeAlias(_) | DeclKind::Struct(_))
			}))
		};
		let provided = |definition| is_compiler_provided(&a.sema, definition);
		// A package function of core's is supplied by the compiler; a core
		// function with a body, even one calling it, is an ordinary one.
		assert!(provided(function("transmute")));
		assert!(!provided(function("slice_from_parts")));
		// Primitives and literal kinds are bodiless; `Char` is a struct core
		// writes.
		assert!(provided(ty("u32")));
		assert!(provided(ty("const_int")));
		assert!(!provided(ty("Char")));
		// `Slice::len` is a bodiless trait function lowering expands.
		let len = a.sema.decls.intrinsics.slice_len.unwrap();
		assert!(provided(Definition::Member(MemberKind::Function(len))));
		// The user's own function is not.
		assert!(!provided(function("f")));
	}

	#[test]
	fn resolutions_in_lists_one_entry_per_name_in_source_order() {
		let a = Analysis::clean(indoc! {"
			func take(x: u32) {}
			func f(x: u32) {
				take{ x };
			}
		"});
		let found: Vec<_> = resolutions_in(&a.references, a.file).collect();
		let spans: Vec<_> = found.iter().map(|(span, _)| span.span).collect();
		let mut sorted = spans.clone();
		sorted.sort();
		sorted.dedup();
		assert_eq!(spans, sorted, "ordered, without a repeated name");
		// The shorthand is a label and a value at one name; the value wins.
		let shorthand = a.span("{ x }", "x");
		let at_shorthand: Vec<_> = found
			.iter()
			.filter(|&&(span, _)| span == shorthand)
			.map(|&(_, reference)| reference)
			.collect();
		assert_eq!(at_shorthand, [a.value("{ x }", "x")]);
	}

	#[test]
	fn symbol_at_returns_the_resolved_reference_and_the_names_span() {
		let marked = Marked::new(indoc! {"
			func $[make]make(amount: i32) -> i32 { amount }
			func main() {
				local amount: i32 = 1;
				_ = $[call]make{ $[label]amount: 3 };
				_ = make{ $[short]amount };
			}
		"});
		let analysis = Analysis::clean(&marked.source);
		let at = |label: &str| {
			let span = marked.name(label);
			let (found, reference) =
				symbol_at(&analysis.references, analysis.file, span.start + 1)
					.unwrap_or_else(|| panic!("nothing at `{label}`"));
			assert_eq!(found, SourceSpan::new(analysis.file, span));
			reference
		};

		// A call names the function, whose kind is read through the sema.
		let Reference::Item {
			item: key,
			route: Route::Direct,
		} = at("call")
		else {
			panic!("expected a declaration");
		};
		assert!(matches!(
			analysis.sema.declaration_kind(key),
			DeclKind::Function(_)
		));
		// A named argument's label is the parameter, not a read of it.
		assert!(matches!(at("label"), Reference::Parameter { .. }));
		// A shorthand argument is a label and the value it supplies: the
		// value is what the name means where it is used.
		assert!(matches!(at("short"), Reference::Local { .. }));
	}
}
