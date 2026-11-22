//! Names a declaration lists, to be filled in: the arguments of a call or a
//! loop's next state by name, a struct pattern's fields, and the entries of
//! a bound's `where { .. }` block. Each is offered in the order its
//! declaration lists it, and is never a call. A name written already is
//! not offered again: written twice, it is reported.

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{CompletionItem, CompletionItemLabelDetails};
use wx_compiler::symbols::Keyword;
use wx_compiler::tir::{Definition, MemberKind, TypeIndex};

use super::{
	ArgumentTarget, Entry, Order, Request, SlotSite, as_trait, candidate,
	with_type,
};
use crate::call;
use crate::query;
use crate::snapshot::Snapshot;

/// The names `site` can still take at the cursor.
pub(super) fn complete(
	request: &mut Request,
	site: SlotSite,
) -> Option<Vec<CompletionItem>> {
	let (file, declaration) = (request.file, request.declaration);
	let label_details = request.options.label_details;
	let snapshot = &mut *request.snapshot;
	let references = &snapshot.references;
	match site {
		// Each field's type on the type the pattern was checked against.
		SlotSite::PatternField {
			pattern,
			owner,
			written,
		} => {
			let (_, reference) =
				query::symbol_at(references, file, owner.start)?;
			let sema = &mut snapshot.sema;
			let fields = sema.pattern_field_names(reference.definition());
			let ast = snapshot.compilation.ast(file);
			let checked = declaration
				.and_then(|declaration| query::body_of(sema, declaration))
				.and_then(|body_owner| {
					let body = sema.owner_body(body_owner)?;
					Some((body_owner, body.pattern_type_of(ast, pattern)?))
				});
			let mut types = Vec::new();
			if let Some((body_owner, ty)) = checked {
				for &(name, definition) in &fields {
					if let Definition::Field { field, .. } = definition
						&& let Some(field_ty) = sema.field_type(ty, field)
						&& let Some(field_ty) = sema.normalize_in_body(
							&snapshot.strings,
							body_owner,
							field_ty,
						) {
						types.push((Some(name), field_ty));
					}
				}
			}
			Some(slot_items(
				snapshot,
				fields,
				&written,
				&types,
				label_details,
			))
		}
		SlotSite::Argument {
			target: ArgumentTarget::Loop { jump },
			written,
		} => {
			let ast = snapshot.compilation.ast(file);
			let sema = &snapshot.sema;
			let owner = query::body_of(sema, declaration?)?;
			let body = sema.owner_body(owner)?;
			let target = body.continue_target(ast, jump)?;
			let mut names = Vec::new();
			let mut types = Vec::new();
			for local in body.scope_locals(body.target_scope(target)) {
				let name = body.local(local).name.inner;
				types.push((Some(name), body.local(local).ty));
				// A name the parser reported missing is no name to give.
				if name != Keyword::Error.symbol() {
					names.push((name, Definition::Local { owner, local }));
				}
			}
			Some(slot_items(snapshot, names, &written, &types, label_details))
		}
		SlotSite::Argument {
			target: ArgumentTarget::Call {
				call,
				callee,
				given,
			},
			written,
		} => {
			let ast = snapshot.compilation.ast(file);
			let sema = &mut snapshot.sema;
			let (_, reference) =
				query::symbol_at(references, file, callee.start)?;
			let names = sema.argument_names(reference.definition(), given);
			// Names and visibility still come from the checker's contract.
			// Only their displayed types use this call's inferred arguments.
			let types = query::body_of(sema, declaration?)
				.and_then(|owner| {
					call::signature(sema, &snapshot.strings, owner, ast, call)
				})
				.map(|signature| signature.parameters)
				.unwrap_or_default();
			Some(slot_items(snapshot, names, &written, &types, label_details))
		}
		// An inherited member names its trait, as a method does; a constant
		// in an entry not marked yet inserts its `const`.
		SlotSite::Binding {
			bound,
			entry,
			written,
		} => {
			let (_, reference) =
				query::symbol_at(references, file, bound.start)?;
			let Definition::Item(bound) = reference.definition() else {
				return None;
			};
			let bindings = snapshot.sema.binding_names(bound, entry.tiers());
			let items = (bindings.into_iter())
				.filter(|binding| {
					!written.contains(&(binding.member.tier(), binding.name))
				})
				.enumerate()
				.map(|(at, binding)| {
					let definition = Definition::Member(binding.member);
					let mut item = slot_item(
						snapshot,
						binding.name,
						definition,
						at,
						None,
						label_details,
					);
					if let (Entry::Unmarked, MemberKind::Constant(_)) =
						(entry, binding.member)
					{
						item.insert_text =
							Some(format!("const {}", item.label));
						item.filter_text = Some(item.label.clone());
					}
					if label_details && let Some(from) = binding.inherited_from
					{
						item.label_details = Some(CompletionItemLabelDetails {
							detail: as_trait(snapshot, from),
							description: None,
						});
					}
					item
				})
				.collect();
			Some(items)
		}
	}
}

/// The items of `names` not `written` yet, in order, each with its type
/// from `types` when it lists one.
fn slot_items(
	snapshot: &Snapshot,
	names: Vec<(SymbolU32, Definition)>,
	written: &[SymbolU32],
	types: &[(Option<SymbolU32>, TypeIndex)],
	label_details: bool,
) -> Vec<CompletionItem> {
	(names.into_iter())
		.filter(|(name, _)| !written.contains(name))
		.enumerate()
		.map(|(at, (name, definition))| {
			let ty = types
				.iter()
				.find(|&&(listed, _)| listed == Some(name))
				.map(|&(_, ty)| ty);
			slot_item(snapshot, name, definition, at, ty, label_details)
		})
		.collect()
}

/// A name `definition` is listed as, at `at` in its declaration's order;
/// `ty` is its type here, shown as `name: Type` and, with `label_details`,
/// beside the name.
fn slot_item(
	snapshot: &Snapshot,
	name: SymbolU32,
	definition: Definition,
	at: usize,
	ty: Option<TypeIndex>,
	label_details: bool,
) -> CompletionItem {
	let mut item = candidate(snapshot, name, definition, Order::Listed(at));
	if let Some(ty) = ty {
		with_type(snapshot, &mut item, ty, label_details);
	}
	item
}
