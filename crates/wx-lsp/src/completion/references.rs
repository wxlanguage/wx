//! Names that mean something at the cursor: a bare name, a path's segment,
//! a member after `.`, a trait's member, a `use` path's last segment, and a
//! jump's label. A function, method or constructor written as a value is
//! offered as its call.

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{
	CompletionItem, CompletionItemLabelDetails, InsertTextFormat,
};
use wx_compiler::tir::{
	DeclKind, Definition, MemberKind, MemberOwner, NameUse, TargetKind,
	TypeIndex,
};

use super::{
	Insert, Jump, Order, ReferenceSite, Request, Within, after_name, as_trait,
	candidate, type_beside, with_type,
};
use crate::hover;
use crate::query;
use crate::snapshot::Snapshot;

/// The names `site` can be at the cursor.
pub(super) fn complete(
	request: &mut Request,
	site: ReferenceSite,
) -> Option<Vec<CompletionItem>> {
	let Request {
		snapshot,
		file,
		offset,
		within,
		declaration,
		use_scope,
		options,
	} = request;
	let (file, offset, declaration, use_scope) =
		(*file, *offset, *declaration, *use_scope);
	let label_details = options.label_details;
	let ast = snapshot.compilation.ast(file);
	// A function, method or constructor written as a value is inserted as its
	// call, unless the call is written already (`hel|per()`).
	let source = &snapshot.compilation.files.get(file).ok()?.source;
	let suffix =
		after_name(source, snapshot.compilation.comments(file), offset);
	let called = suffix.starts_with('(');
	let insert = match site {
		ReferenceSite::Name(NameUse::Value)
		| ReferenceSite::Segment {
			used_as: NameUse::Value,
			..
		}
		| ReferenceSite::TraitMember {
			used_as: NameUse::Value,
			..
		}
		| ReferenceSite::Member { .. }
			if options.snippets && !called =>
		{
			Insert::Call
		}
		_ => Insert::Name,
	};
	let sema = &mut snapshot.sema;
	let references = &snapshot.references;
	let names = match site {
		ReferenceSite::Name(used_as) => match within {
			Within::Body(_) => sema.names_at(
				query::body_of(sema, declaration?)?,
				offset,
				used_as,
			),
			Within::Signature(_) => {
				sema.names_in_signature(declaration?, used_as)
			}
			Within::Use(_) => sema.names_in_scope(use_scope?, used_as),
		},
		// What the prefix means, as checking resolved it; a prefix that did
		// not resolve has nothing after it.
		ReferenceSite::Segment { prefix, used_as } => {
			let (_, reference) =
				query::symbol_at(references, file, prefix.start)?;
			let prefix = reference.definition();
			let mut names = match prefix {
				Definition::Item(loc) => {
					let accessor = match use_scope {
						Some(scope) => scope,
						None => sema.declaration_scope(declaration?)?,
					};
					sema.names_in(accessor, loc, used_as)
				}
				_ => Vec::new(),
			};
			// After a type, its members, which a `use` cannot name. The walk
			// finds what the type's namespace binds (an enum's variant) first.
			if let Some(declaration) = declaration {
				let members = sema.type_member_names(
					&snapshot.strings,
					declaration,
					prefix,
					used_as,
				);
				for (name, definition) in members {
					if !names.iter().any(|&(listed, _)| listed == name) {
						names.push((name, definition));
					}
				}
			}
			names
		}
		// A name a group lists already would be bound twice.
		ReferenceSite::Import { prefix, written } => {
			let (_, reference) =
				query::symbol_at(references, file, prefix.start)?;
			let Definition::Item(prefix) = reference.definition() else {
				return None;
			};
			sema.names_in(use_scope?, prefix, NameUse::Import)
				.into_iter()
				.filter(|(name, _)| !written.contains(name))
				.collect()
		}
		ReferenceSite::TraitMember {
			trait_name,
			used_as,
		} => {
			let (_, reference) =
				query::symbol_at(references, file, trait_name.start)?;
			let Definition::Item(bound) = reference.definition() else {
				return None;
			};
			sema.trait_member_names(bound, used_as)
		}
		// In the order the checker lists them, their receiver written: a
		// method's call gives the arguments after `self`.
		ReferenceSite::Member { object } => {
			let owner = query::body_of(sema, declaration?)?;
			let body = sema.owner_body(owner)?;
			let receiver = body.operand_ty(body.operand_of(ast, object)?);
			let members = sema.member_names(&snapshot.strings, owner, receiver);
			// A field's type on this receiver, its type arguments in place.
			let types: Vec<Option<TypeIndex>> = members
				.iter()
				.map(|&(_, definition)| {
					let Definition::Field { field, .. } = definition else {
						return None;
					};
					let ty = sema.field_type(receiver, field)?;
					sema.normalize_in_body(&snapshot.strings, owner, ty)
				})
				.collect();
			let items = (members.into_iter().zip(types).enumerate())
				.map(|(at, ((name, definition), ty))| {
					let arguments = match definition {
						Definition::Member(MemberKind::Method(function)) => {
							Some(
								snapshot.sema.decls.functions
									[usize::from(function)]
								.params
								.len()
									- 1,
							)
						}
						_ => arguments(snapshot, definition),
					};
					let mut item = value_item(
						snapshot,
						name,
						definition,
						Order::Listed(at),
						insert,
						arguments,
						label_details,
					);
					if let Some(ty) = ty {
						with_type(snapshot, &mut item, ty, label_details);
					}
					item
				})
				.collect();
			return Some(items);
		}
		ReferenceSite::Label(jump) => {
			let owner = query::body_of(sema, declaration?)?;
			let body = sema.owner_body(owner)?;
			body.labels_at(offset)
				.into_iter()
				.filter(|&target| match jump {
					Jump::Break => true,
					// A `continue` restarts only a loop.
					Jump::Continue => {
						body.target_kind(target) == TargetKind::Loop
					}
				})
				.map(|target| {
					let label = body.target(target).label.unwrap();
					(label.inner, Definition::Label { owner, target })
				})
				.collect()
		}
	};
	Some(
		names
			.into_iter()
			.map(|(name, definition)| {
				value_item(
					snapshot,
					name,
					definition,
					Order::ByName,
					insert,
					arguments(snapshot, definition),
					label_details,
				)
			})
			.collect(),
	)
}

/// `reference_item`, and for a name that holds a value, its type beside
/// it.
fn value_item(
	snapshot: &Snapshot,
	name: SymbolU32,
	definition: Definition,
	order: Order,
	insert: Insert,
	arguments: Option<usize>,
	label_details: bool,
) -> CompletionItem {
	let mut item = reference_item(
		snapshot,
		name,
		definition,
		order,
		insert,
		arguments,
		label_details,
	);
	if let Some(ty) = hover::value_type(&snapshot.sema, definition) {
		type_beside(snapshot, &mut item, ty, label_details);
	}
	item
}

/// How many arguments a call of `definition` named through a path writes:
/// every parameter of a function or method, every field of a struct's
/// constructor. `None` for what is not called.
pub(super) fn arguments(
	snapshot: &Snapshot,
	definition: Definition,
) -> Option<usize> {
	let decls = &snapshot.sema.decls;
	match definition {
		Definition::Member(
			MemberKind::Function(function) | MemberKind::Method(function),
		) => Some(decls.functions[usize::from(function)].params.len()),
		Definition::Item(loc) => match snapshot.sema.declaration_kind(loc) {
			DeclKind::Function(function) => {
				Some(decls.functions[usize::from(function)].params.len())
			}
			DeclKind::Struct(index) => {
				Some(decls.structs[usize::from(index)].fields.len())
			}
			_ => None,
		},
		_ => None,
	}
}

/// A name that means `definition`, written as `insert` says; one that is
/// called gives `arguments` to its call. With `label_details`, it shows
/// the trait a method comes from and, for a declaration, its compact form.
pub(super) fn reference_item(
	snapshot: &Snapshot,
	name: SymbolU32,
	definition: Definition,
	order: Order,
	insert: Insert,
	arguments: Option<usize>,
	label_details: bool,
) -> CompletionItem {
	let mut item = candidate(snapshot, name, definition, order);
	if let Some(arguments) = arguments {
		call_item(&mut item, insert, arguments);
	}
	if label_details {
		let trait_index = match definition {
			Definition::Member(MemberKind::Method(function)) => {
				match snapshot.sema.decls.functions[usize::from(function)].owner
				{
					MemberOwner::Trait(index) => Some(index),
					MemberOwner::TraitImpl(index) => {
						snapshot.sema.trait_impl_trait(index)
					}
					MemberOwner::Free | MemberOwner::InherentImpl(_) => None,
				}
			}
			_ => None,
		};
		let detail = trait_index.and_then(|index| as_trait(snapshot, index));
		let description =
			(snapshot.sema.definition_formatter(&snapshot.strings))
				.summary(definition);
		if detail.is_some() || description.is_some() {
			item.label_details = Some(CompletionItemLabelDetails {
				detail,
				description,
			});
		}
	}
	item
}

/// `item`, a name that is called with `arguments`, labelled with its
/// parentheses and inserted as `insert` says. The call punctuation uses the
/// primary label's colour; filtering and insertion use the name, including
/// when a call is written already.
fn call_item(item: &mut CompletionItem, insert: Insert, arguments: usize) {
	let label = std::mem::take(&mut item.label);
	item.label = match arguments {
		0 => format!("{label}()"),
		_ => format!("{label}(…)"),
	};
	item.insert_text = Some(match insert {
		Insert::Call => match arguments {
			0 => format!("{label}()"),
			_ => format!("{label}($1)"),
		},
		Insert::Name => label.clone(),
	});
	if let Insert::Call = insert {
		item.insert_text_format = Some(InsertTextFormat::SNIPPET);
	}
	item.filter_text = Some(label);
}
