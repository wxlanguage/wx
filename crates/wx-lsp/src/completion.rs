use std::collections::{HashMap, HashSet};

use string_interner::symbol::SymbolU32;
use tower_lsp_server::ls_types::{
	CompletionItem, CompletionItemKind, InsertTextFormat,
};
use wx_compiler::ast::StringInterner;
use wx_compiler::tir::{
	ImplEntry, ImplTarget, NamespaceIndex, TIR, TypeFormatter,
};
use wx_compiler::vfs::FileId;

use crate::symbol_index::{ImplRef, SymbolIndex, SymbolKind};

#[cfg_attr(debug_assertions, derive(Debug))]
#[derive(PartialEq)]
pub enum CompletionContext {
	/// Cursor is in expression/statement position. Prefix may be empty (blank trigger).
	Identifier,
	/// Cursor is after `.` — show fields and methods of the receiver type.
	/// `receiver_end` is the exclusive-end byte offset of the receiver text in source.
	DotAccess { receiver_end: usize },
	/// Cursor is after `::` — show module members, enum variants, or associated items.
	/// `lhs_end` is the exclusive-end byte offset of the LHS name in source.
	PathAccess { lhs_end: usize },
	/// Cursor is in a type annotation position (after `:` that is not `::`).
	TypeAnnotation,
}

/// Classifies the completion trigger context at `offset` bytes into `source`.
pub fn classify_context(source: &str, offset: usize) -> CompletionContext {
	// Strip the identifier prefix currently being typed.
	let prefix_start = source[..offset]
		.bytes()
		.rposition(|b| !b.is_ascii_alphanumeric() && b != b'_')
		.map_or(0, |i| i + 1);

	// Everything before the prefix, with trailing ASCII whitespace removed.
	let before = source[..prefix_start]
		.trim_end_matches(|c: char| c.is_ascii_whitespace());

	if before.is_empty() {
		return CompletionContext::Identifier;
	}

	let before_bytes = before.as_bytes();

	match before_bytes[before_bytes.len() - 1] {
		b'.' => {
			let before_dot = before[..before.len() - 1]
				.trim_end_matches(|c: char| c.is_ascii_whitespace());
			CompletionContext::DotAccess {
				receiver_end: before_dot.len(),
			}
		}
		b':' if before_bytes.len() >= 2
			&& before_bytes[before_bytes.len() - 2] == b':' =>
		{
			let before_colons = before[..before.len() - 2]
				.trim_end_matches(|c: char| c.is_ascii_whitespace());
			CompletionContext::PathAccess {
				lhs_end: before_colons.len(),
			}
		}
		b':' => CompletionContext::TypeAnnotation,
		_ => CompletionContext::Identifier,
	}
}

pub fn find_enclosing_function(
	tir: &TIR,
	file_id: FileId,
	cursor_offset: u32,
) -> Option<usize> {
	tir.functions.iter().position(|f| {
		f.file_id == file_id
			&& f.body.as_ref().is_some_and(|body| {
				let span = body.stack.scopes[0].span;
				span.start <= cursor_offset && span.end > cursor_offset
			})
	})
}

/// Collects completion items for all locals visible at `cursor_offset` inside the given function.
/// Walks the innermost scope containing the cursor, then follows the parent chain upward.
pub fn local_completion_items(
	tir: &TIR,
	func_index: usize,
	interner: &StringInterner,
	cursor_offset: u32,
	prefix: &str,
) -> Vec<CompletionItem> {
	let formatter = TypeFormatter::new(tir, interner);
	let function = &tir.functions[func_index];
	let body = match &function.body {
		Some(b) => b,
		None => return vec![],
	};
	let num_params = function.params.len();

	let innermost_idx = body
		.stack
		.scopes
		.iter()
		.enumerate()
		.filter(|(_, s)| {
			s.span.start <= cursor_offset && s.span.end > cursor_offset
		})
		.min_by_key(|(_, s)| s.span.end - s.span.start)
		.map(|(i, _)| i as u32);

	let innermost_idx = match innermost_idx {
		Some(i) => i,
		None => return vec![],
	};

	let mut items = vec![];
	let mut current = Some(innermost_idx);

	while let Some(scope_idx) = current {
		let scope = &body.stack.scopes[scope_idx as usize];
		let is_innermost = scope_idx == innermost_idx;
		let is_root = scope_idx == 0;

		for (local_idx, local) in scope.locals.iter().enumerate() {
			let is_param = is_root && local_idx < num_params;
			// In the innermost scope, skip locals not yet declared (except params which
			// are always in scope). Ancestor-scope locals are always visible.
			if !is_param
				&& is_innermost
				&& local.name.span.start >= cursor_offset
			{
				continue;
			}
			let name = match interner.resolve(local.name.inner) {
				Some(n) => n,
				None => continue,
			};
			if !name.starts_with(prefix) {
				continue;
			}
			let detail = formatter.display_type(local.ty).ok();
			// `0_` sorts before `global_completion_items`' `1_` prefix, so
			// locals are listed first regardless of alphabetical label order.
			let sort_text = Some(format!("0_{name}"));
			items.push(CompletionItem {
				label: name.to_string(),
				kind: Some(CompletionItemKind::VARIABLE),
				detail,
				sort_text,
				..Default::default()
			});
		}

		current = scope.parent;
	}

	items
}

/// Namespace of the module containing `file_id`, for completion requests
/// that fall outside any function body (no enclosing-function namespace to
/// fall back on). Only inline `module foo { }` blocks are missed here —
/// those share the file of their enclosing function, which already carries
/// the right namespace.
fn file_namespace(tir: &TIR, file_id: FileId) -> Option<NamespaceIndex> {
	tir.module_decls
		.iter()
		.find(|decl| decl.own_file_id == Some(file_id))
		.map(|decl| decl.namespace_idx)
}

/// The set of namespaces whose direct symbols are visible from `start`:
/// `start` itself, its `use path::*` wildcard imports, then each ancestor
/// namespace (and its wildcard imports) up to the implicit root. Mirrors the
/// walk `lookup_global_symbol` performs in the type checker, but collects
/// every reachable namespace instead of stopping at the first name match.
pub fn visible_namespaces(
	tir: &TIR,
	start: Option<NamespaceIndex>,
) -> HashSet<Option<NamespaceIndex>> {
	let mut visible = HashSet::new();
	let mut current = start;
	loop {
		if !visible.insert(current) {
			break;
		}
		match current {
			Some(idx) => {
				let ns = &tir.namespaces[idx as usize];
				visible.extend(ns.wildcard_imports.iter().map(|&i| Some(i)));
				current = ns.parent;
			}
			None => {
				visible
					.extend(tir.root_wildcard_imports.iter().map(|&i| Some(i)));
				break;
			}
		}
	}
	visible
}

/// Maps a `global_definitions` entry to its `CompletionItem`, without the
/// `sort_text` bare-identifier completion prefixes on top (see callers).
/// Shared between `global_completion_items` and `path_completion_items`'s
/// `Namespace::` branch — both list a namespace's direct members, just
/// filtered differently (visibility vs. exact namespace match).
fn global_definition_completion_item(
	tir: &TIR,
	name: String,
	kind: &SymbolKind,
) -> Option<CompletionItem> {
	Some(match kind {
		SymbolKind::Function(def_id) => {
			let fi = tir.function_index(*def_id)? as usize;
			let func = &tir.functions[fi];
			let (insert_text, insert_text_format) = if func.params.is_empty() {
				(format!("{}()", name), InsertTextFormat::PLAIN_TEXT)
			} else {
				(format!("{}($1)", name), InsertTextFormat::SNIPPET)
			};
			CompletionItem {
				label: name,
				kind: Some(CompletionItemKind::FUNCTION),
				insert_text: Some(insert_text),
				insert_text_format: Some(insert_text_format),
				..Default::default()
			}
		}
		SymbolKind::Global(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::VARIABLE),
			..Default::default()
		},
		SymbolKind::Const(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::CONSTANT),
			..Default::default()
		},
		SymbolKind::Struct(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::STRUCT),
			..Default::default()
		},
		SymbolKind::Enum(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::ENUM),
			..Default::default()
		},
		// Never reached: `EnumVariant` is never pushed into
		// `global_definitions` — it's only ever accessed as a
		// qualified `Enum::Variant` member, never bare.
		SymbolKind::Namespace(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::MODULE),
			..Default::default()
		},
		SymbolKind::Trait(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::INTERFACE),
			..Default::default()
		},
		SymbolKind::TypeSet(_) => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::TYPE_PARAMETER),
			..Default::default()
		},
		SymbolKind::AssocType { .. } => CompletionItem {
			label: name,
			kind: Some(CompletionItemKind::TYPE_PARAMETER),
			..Default::default()
		},
		_ => return None,
	})
}

/// Prefix-searches `symbol_index.global_definitions` and maps each match visible
/// from `visible_from` to a `CompletionItem`.
pub fn global_completion_items(
	tir: &TIR,
	interner: &StringInterner,
	symbol_index: &SymbolIndex,
	prefix: &str,
	visible_from: &HashSet<Option<NamespaceIndex>>,
) -> Vec<CompletionItem> {
	let lower = symbol_index.global_definitions.partition_point(|def| {
		interner.resolve(def.name).unwrap_or("") < prefix
	});

	symbol_index.global_definitions[lower..]
		.iter()
		.take_while(|def| {
			interner.resolve(def.name).unwrap_or("").starts_with(prefix)
		})
		.filter(|def| visible_from.contains(&def.namespace))
		.filter_map(|def| {
			let name = interner.resolve(def.name)?.to_string();
			let item =
				global_definition_completion_item(tir, name, &def.info.kind)?;
			// Sorts after `local_completion_items`' `0_` prefix, so locals
			// in scope are listed before same-prefix globals.
			Some(CompletionItem {
				sort_text: Some(format!("1_{}", item.label)),
				..item
			})
		})
		.collect()
}

/// Kinds valid in type position. Doesn't yet distinguish a plain type
/// annotation from a bound (`T: Trait`) — both currently get this same,
/// type-only list, so a bound position won't offer `Trait`/`TypeSet` names
/// the way it ideally should; narrowing that further needs detecting
/// whether the colon sits inside a `<...>` list, which is out of scope for
/// now (see `CompletionContext::TypeAnnotation`'s doc comment). Doesn't
/// cover primitive type names (`i32`, `bool`, ...) either — those aren't
/// `SymbolKind`s today, but are expected to become ordinary stdlib items
/// once primitives move to intrinsics, at which point this list picks them
/// up automatically with no changes needed here.
fn is_type_like(kind: &SymbolKind) -> bool {
	matches!(
		kind,
		SymbolKind::Struct(_)
			| SymbolKind::Enum(_)
			| SymbolKind::TypeSet(_)
			| SymbolKind::Namespace(_)
	)
}

/// Like `global_completion_items`, but restricted to kinds valid in type
/// position (see `is_type_like`). Doesn't yet include in-scope type
/// parameters — unlike locals, those aren't in `global_definitions` at all
/// (it explicitly excludes scope-sensitive items), so offering them needs a
/// separate walk of the enclosing function's own + inherited type params,
/// the way `local_completion_items` walks scopes for locals.
pub fn type_completion_items(
	tir: &TIR,
	interner: &StringInterner,
	symbol_index: &SymbolIndex,
	prefix: &str,
	visible_from: &HashSet<Option<NamespaceIndex>>,
) -> Vec<CompletionItem> {
	let lower = symbol_index.global_definitions.partition_point(|def| {
		interner.resolve(def.name).unwrap_or("") < prefix
	});
	symbol_index.global_definitions[lower..]
		.iter()
		.take_while(|def| {
			interner.resolve(def.name).unwrap_or("").starts_with(prefix)
		})
		.filter(|def| visible_from.contains(&def.namespace))
		.filter(|def| is_type_like(&def.info.kind))
		.filter_map(|def| {
			let name = interner.resolve(def.name)?.to_string();
			global_definition_completion_item(tir, name, &def.info.kind)
		})
		.collect()
}

/// Maps every entry in an impl block's/trait impl's/trait's own `members`
/// map to a `CompletionItem`, gated on `pub_span.is_some()` — per the "`pub
/// fn` only" rule (see `Common pitfalls` in `CLAUDE.md`): a non-`pub` member
/// isn't reachable via `Type::name()` at all, so it shouldn't complete as if
/// it were.
fn member_completion_items(
	tir: &TIR,
	interner: &StringInterner,
	members: &HashMap<SymbolU32, ImplEntry>,
	prefix: &str,
) -> Vec<CompletionItem> {
	members
		.iter()
		.filter_map(|(name_sym, entry)| {
			let name = interner.resolve(*name_sym)?;
			if !name.starts_with(prefix) {
				return None;
			}
			match entry {
				ImplEntry::Method(fi) => {
					let func = tir.functions.get(*fi as usize)?;
					func.pub_span?;
					let insert_text = if func.params.len() <= 1 {
						format!("{name}()")
					} else {
						format!("{name}($1)")
					};
					Some(CompletionItem {
						label: name.to_string(),
						kind: Some(CompletionItemKind::METHOD),
						insert_text: Some(insert_text),
						insert_text_format: Some(if func.params.len() <= 1 {
							InsertTextFormat::PLAIN_TEXT
						} else {
							InsertTextFormat::SNIPPET
						}),
						..Default::default()
					})
				}
				ImplEntry::AssocFunction(fi) => {
					let func = tir.functions.get(*fi as usize)?;
					func.pub_span?;
					let insert_text = if func.params.is_empty() {
						format!("{name}()")
					} else {
						format!("{name}($1)")
					};
					Some(CompletionItem {
						label: name.to_string(),
						kind: Some(CompletionItemKind::FUNCTION),
						insert_text: Some(insert_text),
						insert_text_format: Some(if func.params.is_empty() {
							InsertTextFormat::PLAIN_TEXT
						} else {
							InsertTextFormat::SNIPPET
						}),
						..Default::default()
					})
				}
				ImplEntry::AssocConstant(ci) => {
					let constant = tir.constants.get(*ci as usize)?;
					constant.pub_span?;
					Some(CompletionItem {
						label: name.to_string(),
						kind: Some(CompletionItemKind::CONSTANT),
						..Default::default()
					})
				}
				ImplEntry::AssocType { .. } => Some(CompletionItem {
					label: name.to_string(),
					kind: Some(CompletionItemKind::TYPE_PARAMETER),
					..Default::default()
				}),
			}
		})
		.collect()
}

/// Every impl block/trait impl targeting `target`'s member completions,
/// merged — via `SymbolIndex::impls_by_target`, the same `ImplTarget`-keyed
/// reverse index `reference_search_kinds`/`implementation_locations` use, so
/// this stays O(1) instead of scanning every impl in the program.
fn impl_member_completion_items(
	tir: &TIR,
	interner: &StringInterner,
	symbol_index: &SymbolIndex,
	target: ImplTarget,
	prefix: &str,
) -> Vec<CompletionItem> {
	symbol_index
		.impls_by_target
		.get(&target)
		.into_iter()
		.flatten()
		.flat_map(|r| {
			let members = match r {
				ImplRef::Inherent(idx) => {
					tir.inherent_impls.get(*idx as usize).map(|b| &b.members)
				}
				ImplRef::Trait(idx) => {
					tir.trait_impls.get(*idx as usize).map(|ti| &ti.members)
				}
			};
			members
				.into_iter()
				.flat_map(|m| member_completion_items(tir, interner, m, prefix))
		})
		.collect()
}

/// Resolves a single bare identifier (no `::` of its own) to the `SymbolKind`
/// it names, the same way `global_completion_items` looks names up — via
/// `symbol_index.global_definitions`, taking the first match visible from
/// `visible`. Ambiguity (the same name visible from two different reachable
/// namespaces) is vanishingly rare for type/namespace names in practice, so
/// "first visible match" is good enough rather than reimplementing the
/// compiler's full shadowing precedence here.
fn resolve_bare_name(
	symbol_index: &SymbolIndex,
	interner: &StringInterner,
	name: &str,
	visible: &HashSet<Option<NamespaceIndex>>,
) -> Option<SymbolKind> {
	let lower = symbol_index
		.global_definitions
		.partition_point(|def| interner.resolve(def.name).unwrap_or("") < name);
	symbol_index.global_definitions[lower..]
		.iter()
		.take_while(|def| interner.resolve(def.name).unwrap_or("") == name)
		.find(|def| visible.contains(&def.namespace))
		.map(|def| def.info.kind)
}

/// Completions after `Type::`/`namespace::`/`Trait::`. `lhs_end` is the
/// exclusive-end byte offset of everything before the `::` (see
/// `classify_context`) — only a single bare identifier immediately before it
/// is handled; a deeper path (`a::b::`) bails out to no completions, same as
/// the `DotAccess`/`PathAccess` TODOs this replaces did.
fn path_completion_items(
	tir: &TIR,
	interner: &StringInterner,
	symbol_index: &SymbolIndex,
	source: &str,
	lhs_end: usize,
	prefix: &str,
	visible: &HashSet<Option<NamespaceIndex>>,
) -> Vec<CompletionItem> {
	let lhs_text = &source[..lhs_end];
	let trimmed_end = lhs_text
		.trim_end_matches(|c: char| c.is_ascii_whitespace())
		.len();
	let trimmed = &lhs_text[..trimmed_end];
	let ident_start = trimmed
		.bytes()
		.rposition(|b| !b.is_ascii_alphanumeric() && b != b'_')
		.map_or(0, |i| i + 1);
	// `a::b::` — the identifier right before `::` is itself preceded by
	// another `::`. Not yet supported (see doc comment).
	if trimmed[..ident_start].trim_end().ends_with("::") {
		return Vec::new();
	}
	let lhs_name = &trimmed[ident_start..];
	if lhs_name.is_empty() {
		return Vec::new();
	}

	let Some(resolved) =
		resolve_bare_name(symbol_index, interner, lhs_name, visible)
	else {
		return Vec::new();
	};

	match resolved {
		SymbolKind::Namespace(ns_idx) => symbol_index
			.global_definitions
			.iter()
			.filter(|def| def.namespace == Some(ns_idx))
			.filter_map(|def| {
				let name = interner.resolve(def.name)?;
				if !name.starts_with(prefix) {
					return None;
				}
				global_definition_completion_item(
					tir,
					name.to_string(),
					&def.info.kind,
				)
			})
			.collect(),
		SymbolKind::Enum(id) => {
			let mut items = Vec::new();
			if let Some(ei) = tir.enum_index(id) {
				let enum_ = &tir.enums[ei as usize];
				items.extend(enum_.variants.iter().filter_map(|v| {
					let name = interner.resolve(v.name.inner)?;
					if !name.starts_with(prefix) {
						return None;
					}
					Some(CompletionItem {
						label: name.to_string(),
						kind: Some(CompletionItemKind::ENUM_MEMBER),
						..Default::default()
					})
				}));
			}
			if let Some(idx) = tir.enum_index(id) {
				items.extend(impl_member_completion_items(
					tir,
					interner,
					symbol_index,
					ImplTarget::Enum(idx),
					prefix,
				));
			}
			items
		}
		SymbolKind::Struct(id) => {
			tir.struct_index(id).map_or_else(Vec::new, |idx| {
				impl_member_completion_items(
					tir,
					interner,
					symbol_index,
					ImplTarget::Struct(idx),
					prefix,
				)
			})
		}
		SymbolKind::Trait(id) => {
			tir.trait_index(id).map_or_else(Vec::new, |idx| {
				member_completion_items(
					tir,
					interner,
					&tir.traits[idx as usize].members,
					prefix,
				)
			})
		}
		_ => Vec::new(),
	}
}

pub fn completion_items(
	tir: &TIR,
	interner: &StringInterner,
	symbol_index: &SymbolIndex,
	file_id: FileId,
	source: &str,
	offset: usize,
) -> Vec<CompletionItem> {
	let prefix_start = source[..offset]
		.bytes()
		.rposition(|b| !b.is_ascii_alphanumeric() && b != b'_')
		.map_or(0, |i| i + 1);
	let prefix = &source[prefix_start..offset];
	let cursor_offset = offset as u32;
	let func_index = find_enclosing_function(tir, file_id, cursor_offset);
	let current_namespace = match func_index {
		Some(fi) => tir.functions[fi].namespace,
		None => file_namespace(tir, file_id),
	};
	let visible = visible_namespaces(tir, current_namespace);

	match classify_context(source, offset) {
		CompletionContext::Identifier => {
			let mut items = match func_index {
				Some(func_index) => local_completion_items(
					tir,
					func_index,
					interner,
					cursor_offset,
					prefix,
				),
				None => Vec::new(),
			};

			items.extend(global_completion_items(
				tir,
				interner,
				symbol_index,
				prefix,
				&visible,
			));
			items
		}
		CompletionContext::DotAccess { .. } => {
			// TODO: resolve receiver type → impl_block_list + struct fields
			vec![]
		}
		CompletionContext::PathAccess { lhs_end } => path_completion_items(
			tir,
			interner,
			symbol_index,
			source,
			lhs_end,
			prefix,
			&visible,
		),
		CompletionContext::TypeAnnotation => {
			type_completion_items(tir, interner, symbol_index, prefix, &visible)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn empty_source_is_identifier() {
		assert_eq!(classify_context("", 0), CompletionContext::Identifier);
	}

	#[test]
	fn bare_identifier_at_end_is_identifier() {
		assert_eq!(classify_context("foo", 3), CompletionContext::Identifier);
	}

	#[test]
	fn blank_inside_block_is_identifier() {
		let src = "fn add(a: i32, b: i32) -> i32 {\n    ";
		assert_eq!(
			classify_context(src, src.len()),
			CompletionContext::Identifier
		);
	}

	#[test]
	fn partial_identifier_after_operator_is_identifier() {
		assert_eq!(
			classify_context("let x = fo", 10),
			CompletionContext::Identifier
		);
	}

	#[test]
	fn after_open_brace_is_identifier() {
		assert_eq!(classify_context("{ ", 2), CompletionContext::Identifier);
	}

	#[test]
	fn dot_no_prefix_is_dot_access() {
		// "a." — receiver is "a" with exclusive end 1
		assert_eq!(
			classify_context("a.", 2),
			CompletionContext::DotAccess { receiver_end: 1 }
		);
	}

	#[test]
	fn dot_with_partial_field_prefix_is_dot_access() {
		// "foo.bar" at offset 7 — prefix "bar", receiver "foo"
		assert_eq!(
			classify_context("foo.bar", 7),
			CompletionContext::DotAccess { receiver_end: 3 }
		);
	}

	#[test]
	fn dot_with_spaces_is_dot_access() {
		// "foo . " — spaces around dot, receiver_end still points past "foo"
		assert_eq!(
			classify_context("foo . ", 6),
			CompletionContext::DotAccess { receiver_end: 3 }
		);
	}

	#[test]
	fn double_colon_no_prefix_is_path_access() {
		// "Foo::" — lhs exclusive end is 3
		assert_eq!(
			classify_context("Foo::", 5),
			CompletionContext::PathAccess { lhs_end: 3 }
		);
	}

	#[test]
	fn double_colon_with_partial_name_is_path_access() {
		// "math::add" — prefix "add", lhs "math"
		assert_eq!(
			classify_context("math::add", 9),
			CompletionContext::PathAccess { lhs_end: 4 }
		);
	}

	#[test]
	fn single_colon_is_type_annotation() {
		assert_eq!(
			classify_context("x:", 2),
			CompletionContext::TypeAnnotation
		);
	}

	#[test]
	fn colon_after_name_with_space_is_type_annotation() {
		assert_eq!(
			classify_context("local x: ", 9),
			CompletionContext::TypeAnnotation
		);
	}

	#[test]
	fn colon_with_partial_type_is_type_annotation() {
		// "fn f(a: i" — prefix "i"
		assert_eq!(
			classify_context("fn f(a: i", 9),
			CompletionContext::TypeAnnotation
		);
	}

	#[test]
	fn single_colon_not_confused_with_double_colon() {
		// Sanity: "::" is PathAccess, single ":" is TypeAnnotation
		assert_eq!(
			classify_context("Foo::", 5),
			CompletionContext::PathAccess { lhs_end: 3 }
		);
		assert_eq!(
			classify_context("a:", 2),
			CompletionContext::TypeAnnotation
		);
	}

	#[test]
	fn partial_identifier_mid_expression_is_identifier() {
		// "a + b" cursor after "b" — no special trigger
		assert_eq!(classify_context("a + b", 5), CompletionContext::Identifier);
	}
}
