use std::collections::{HashMap, HashSet};

use codespan_reporting::diagnostic::Severity;

use crate::ast::Statement;
use crate::vfs::{Files, PackageGraph, PackageKind};
use crate::{ast::MethodCallExpr, tir::*};

mod aggregates;
mod body;
mod calls;
mod control;
mod generics;
mod literal;
mod memory;
mod modules;
mod operators;
mod paths;
mod prescan;
mod signature;
mod traits;
mod types;

use aggregates::{
	UnknownStructFieldDiagnostic, report_duplicate_struct_field_init,
	report_not_a_struct_type, report_unknown_struct_field,
};
pub use literal::{CharLiteralError, parse_char_literal, unescape_string};
use literal::{
	IntegerLiteralOutOfRangeDiagnostic, report_char_literal_too_long,
	report_empty_char_literal, report_integer_literal_out_of_range,
	report_not_const_evaluatable,
};
use memory::report_cannot_store_through_immutable_pointer;
use modules::{
	DuplicateDefinitionDiagnostic, report_duplicate_definition,
	report_missing_import_alias,
};
use operators::{EvalMode, OperatorTraits};
use paths::{
	report_cannot_take_address_of_value, report_qualified_path_no_such_type,
	report_qualified_path_trait_not_satisfied,
};
use signature::{
	report_missing_function_body, report_non_constant_global_initializer,
};
use traits::report_associated_type_in_inherent_impl;
use types::report_undeclared_type;

struct ExprContext {
	lookup: HashMap<(ScopeIndex, SymbolU32), LocalIndex>,
	scope_index: ScopeIndex,
	stack: StackFrame,
	resolve_context: ResolveContext,
	scope: Option<GenericScope>,
	mode: EvalMode,
}

impl ExprContext {
	fn push_local(&mut self, local: Local) -> LocalIndex {
		let name_symbol = local.name.inner;
		let index = self.stack.push_local(self.scope_index, local);
		self.lookup.insert((self.scope_index, name_symbol), index);
		index
	}

	fn resolve_local(
		&self,
		symbol: SymbolU32,
	) -> Option<(ScopeIndex, LocalIndex)> {
		let mut scope_index = self.scope_index;

		loop {
			if let Some(&value) = self.lookup.get(&(scope_index, symbol)) {
				return Some((scope_index, value));
			}

			scope_index = self.stack.scopes[scope_index as usize].parent?;
		}
	}

	fn enter_block<T>(
		&mut self,
		block: BlockScope,
		handler: impl FnOnce(&mut Self) -> T,
	) -> T {
		let parent_scope_index = self.scope_index;
		self.scope_index = self.stack.scopes.len() as u32;
		self.stack.scopes.push(block);

		let result = handler(self);

		self.scope_index = parent_scope_index;
		result
	}

	fn resolve_label(
		&self,
		symbol: SymbolU32,
	) -> Option<(ScopeIndex, LabelIndex)> {
		let mut scope_index = self.scope_index;

		loop {
			let scope = &self.stack.scopes[scope_index as usize];
			match scope.label {
				Some(label_index)
					if self.stack.labels[label_index as usize].name.inner
						== symbol =>
				{
					return Some((scope_index, label_index));
				}
				_ => {}
			}

			scope_index = scope.parent?;
		}
	}

	fn get_closest_loop_block(&self) -> Option<ScopeIndex> {
		let mut scope_index = self.scope_index;

		loop {
			let scope = &self.stack.scopes[scope_index as usize];
			if scope.kind == BlockKind::Loop {
				return Some(scope_index);
			}

			scope_index = scope.parent?
		}
	}
}

struct Builder<'ast, 'graph> {
	// These cannot collapse into a single `&'graph mut CompilationUnit`, even
	// though all four are its fields. `ast_nodes` holds `&'ast ast::Item`
	// pointing into `packages[..].modules[..].ast` — into the same unit. That
	// only works because `packages` (shared) and `interner`/`id_generator`
	// (mutable) are *disjoint fields* borrowed separately. Behind one `&mut`
	// the AST refs must be reborrowed out of it, which poisons the builder for
	// every later `&mut self` phase (E0502) — and phases 2, 3, 3.5 and 4 all
	// run while `ast_nodes` is live.
	interner: &'graph mut ast::StringInterner,
	id_generator: &'graph mut ast::DefIdGenerator,
	files: &'graph Files,
	/// Read only to resolve what a package calls its dependencies, which is
	/// where a package's canonical name lives (see `PackageGraph::dependency_names`).
	packages: &'graph [PackageGraph],
	/// The package being compiled. Only `export { .. }` needs this: exports
	/// are a property of the artifact as a whole, so the sole legal home for
	/// a block is this package's entry file — a dependency that declares one
	/// would otherwise merge its names into an ABI it doesn't own.
	root_package: PackageId,
	/// The package providing the standard library, whose root namespace is the
	/// prelude every lookup falls back to. See [`Builder::lookup_scope_chain`].
	stdlib_package: PackageId,
	type_index_lookup: HashMap<Type, TypeIndex>,
	tir: TIR,
	/// Populated in Phase 1, in parse order. Index matches `sig_state` entries.
	ast_nodes: Vec<AstEntry<'ast>>,
	/// Maps DefId → SigEntry; populated after Phase 1 with exact capacity.
	sig_state: HashMap<ast::DefId, SigEntry>,
	/// `None` until Phase 2 finishes; see `Builder::operator_traits`.
	operator_traits: Option<OperatorTraits>,
}

#[derive(Clone, Copy, PartialEq)]
enum ComputeState {
	Pending,
	InProgress,
	Done,
}

enum BoundKind {
	Trait(TraitBound),
	TypeSet(TypesetBound),
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
struct AstEntry<'ast> {
	def_id: ast::DefId,
	file_id: FileId,
	namespace: NamespaceIndex,
	node: AstNodeRef<'ast>,
}

#[derive(Clone, Copy)]
struct SigEntry {
	node_idx: usize,
	state: ComputeState,
}

#[derive(Clone, Copy)]
struct GenericScope {
	owner: TypeParamOwner,
	self_type: Option<TypeIndex>,
}

#[derive(Clone, Copy)]
struct ResolveContext {
	file_id: FileId,
	namespace: NamespaceIndex,
}

impl ResolveContext {
	fn new(file_id: FileId, namespace: NamespaceIndex) -> Self {
		Self { file_id, namespace }
	}
}

#[derive(Clone)]
#[cfg_attr(debug_assertions, derive(Debug))]
enum AstNodeRef<'ast> {
	Function {
		item: &'ast ast::Item,
	},
	Struct {
		item: &'ast ast::Item,
	},
	Enum {
		item: &'ast ast::Item,
	},
	Global {
		item: &'ast ast::Item,
	},
	Memory {
		item: &'ast ast::Item,
	},
	Constant {
		item: &'ast ast::Item,
	},
	TypeSet {
		typeset_index: TypesetIndex,
		item: &'ast ast::Item,
	},
	TypeAlias {
		item: &'ast ast::Item,
	},
	Trait {
		trait_index: TraitIndex,
		item: &'ast ast::Item,
	},
	TraitFunction {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	},
	TraitConst {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	},
	TraitAssocType {
		trait_index: TraitIndex,
		item: &'ast ast::TraitItem,
	},
	TraitImplBlock {
		item: &'ast ast::Item,
	},
	TraitImplFunction {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	TraitImplConstant {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	TraitImplAssocType {
		parent_id: ast::DefId,
		item: &'ast ast::ImplItem,
	},
	InherentImplBlock {
		impl_type_params: &'ast [ast::TypeParam],
		impl_target: &'ast ast::Spanned<ast::TypeExpression>,
		block_index: u32,
	},
	InherentImplFunction {
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: u32,
	},
	InherentImplConst {
		block_id: ast::DefId,
		item: &'ast ast::ImplItem,
		block_index: u32,
	},
	ImportedFunction {
		import_module_index: u32,
		decl: &'ast ast::ImportDeclaration,
	},
	ImportedGlobal {
		import_module_index: u32,
		decl: &'ast ast::ImportDeclaration,
	},
	/// One named leaf of a `use` tree. Everything it needs is already in
	/// `tir.use_items[use_index]` — the syntactic prefix, the name, the
	/// alias — so unlike every other variant here it holds no `&'ast`
	/// reference.
	Use {
		use_index: u32,
	},
	/// An `export { .. }` block. Carries no type of its own — its
	/// "signature" is the act of resolving each listed name to an
	/// `ExportItem`, which is why it rides the Phase 2 sweep like any
	/// other item instead of needing a pass of its own.
	Export {
		item: &'ast ast::Item,
	},
}

fn report_unused_enum_variants(
	interner: &ast::StringInterner,
	file_id: FileId,
	unused_variants: &[Spanned<SymbolU32>],
) -> Diagnostic<FileId> {
	let message = match unused_variants.len() {
		1 => {
			let name = interner.resolve(unused_variants[0].inner).unwrap();
			format!("variant `{name}` is never constructed")
		}
		2 => {
			let a = interner.resolve(unused_variants[0].inner).unwrap();
			let b = interner.resolve(unused_variants[1].inner).unwrap();
			format!("variants `{a}` and `{b}` are never constructed")
		}
		3..=5 => {
			let (last, rest) = unused_variants.split_last().unwrap();
			let rest = rest
				.iter()
				.map(|name| {
					format!("`{}`", interner.resolve(name.inner).unwrap())
				})
				.collect::<Vec<_>>()
				.join(", ");
			let last = interner.resolve(last.inner).unwrap();
			format!("variants {rest}, and `{last}` are never constructed")
		}
		_ => "multiple variants are never constructed".to_string(),
	};
	let mut diagnostic = Diagnostic::warning()
		.with_code(DiagnosticCode::UnusedEnumVariant.code())
		.with_message(message);
	for name in unused_variants {
		diagnostic = diagnostic
			.with_label(SourceSpan::new(file_id, name.span).secondary_label());
	}
	diagnostic
}

struct TypeMistmatchDiagnostic {
	expected_type: TypeIndex,
	actual_type: TypeIndex,
	span: SourceSpan,
}

fn report_type_mistmatch(
	fmt: TypeFormatter,
	diagnostic: TypeMistmatchDiagnostic,
) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeMistmatch.code())
		.with_message("type mismatch")
		.with_label(diagnostic.span.primary_label().with_message(format!(
			"expected `{}`, found `{}`",
			fmt.display_type(diagnostic.expected_type).unwrap(),
			fmt.display_type(diagnostic.actual_type).unwrap()
		)))
}

fn report_type_annotation_required(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::TypeAnnotationRequired.code())
		.with_message("type annotation required")
		.with_label(span.primary_label())
}

fn report_unreachable_code(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::warning()
		.with_code(DiagnosticCode::UnreachableCode.code())
		.with_message("unreachable code")
		.with_label(
			span.primary_label()
				.with_message("this code will never be executed"),
		)
}

/// Result of resolving a member name (method, associated fn/const/type) on a
/// concrete type against inherent impls and trait impls. See
/// `Builder::resolve_impl_member`.
///
/// The `Box<[TypeIndex]>` on `Found` is the impl-block-level type
/// substitution inferred for a generic inherent impl (e.g. `T = i32` for
/// `impl<T> Box<T>` when resolving on `Box<i32>`) — empty for a concrete
/// inherent impl block (no type params to solve for) and for trait impls /
/// type-param bounds, which are already resolved against one fixed concrete
/// type and never need one.
/// Governs whether [`Builder::resolve_generic_type_application`] (and the
/// path-resolution helpers that feed it) may pad a short type-argument list
/// with `TypeIndex::INFER`.
///
/// [`Builder::resolve_type`] always resolves via [`Self::RequireExact`],
/// unconditionally — every `ast::TypeExpression::Path`, whatever position it
/// appears in (fn param, impl target, `local` annotation, nested inside
/// `Vec<Pair>`...), is a place with no expression to unify a gap against
/// later, so a short argument list is always an immediate
/// `TypeArgCountMismatch`. Writing `_` explicitly (`Vec<_>`) still resolves
/// fine here — the arity matches, so there's nothing to reject at this
/// layer; whether an explicit `_` is itself allowed to survive is a
/// separate, later check ([`Builder::resolve_signature_type`]'s
/// `contains_infer`, for positions with no expression to infer it from at
/// all).
///
/// [`Self::AllowInfer`] is for the other, syntactically distinct caller of
/// [`Builder::resolve_path_type`]: a raw `&[ast::PathSegment]` in *path*
/// position (struct-init, `Wrapper::<T>::method()`), never routed through
/// `ast::TypeExpression`. These always have a value alongside them (field
/// expressions, call arguments) that a later inference step unifies against,
/// so an omitted argument list is legitimate and gets padded for that step.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TypeArgArity {
	AllowInfer,
	RequireExact,
}

/// A struct field resolved by name — see [`Builder::resolve_struct_field`].
#[derive(Clone, Copy)]
struct ResolvedField {
	index: FieldIndex,
	/// Already substituted with the struct's type arguments, so no caller has
	/// to remember to do it.
	ty: TypeIndex,
}

enum MemberLookup {
	Inherent {
		entry: ImplEntry,
		type_args: Box<[TypeIndex]>,
	},
	Trait {
		entry: ImplEntry,
		type_args: Box<[TypeIndex]>,
		trait_index: TraitIndex,
	},
	Ambiguous,
	NotFound,
}

/// Why [`Builder::resolve_trait_member`] didn't find the requested member —
/// the two genuinely different diagnostics rustc itself distinguishes for
/// `<Type as Trait>::item` (trait-bound-not-satisfied vs. no-such-item), so
/// the caller (which knows whether it's in type or expression position, and
/// therefore which existing diagnostic code applies) can pick the right one
/// instead of getting one blurred "not found."
enum TraitMemberError {
	/// `target_type` isn't bound by / doesn't implement the trait at all.
	NotImplemented,
	/// It does implement the trait, but the trait has no such member.
	NoSuchMember,
}

fn report_undeclared_identifier(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::UndeclaredIdentifier.code())
		.with_message("undeclared identifier")
		.with_label(span.primary_label())
}

fn report_cannot_mutate_immutable(span: SourceSpan) -> Diagnostic<FileId> {
	Diagnostic::error()
		.with_code(DiagnosticCode::CannotMutateImmutable.code())
		.with_message("cannot mutate immutable binding")
		.with_label(span.primary_label())
}

pub fn build(graph: &mut CompilationUnit) -> TIR {
	let source_modules: Vec<_> = graph
		.packages
		.iter()
		.flat_map(|package_graph| package_graph.modules.iter())
		.collect();
	assert!(
		!source_modules.is_empty(),
		"TIR::build requires at least one AST"
	);

	let tir = TIR {
		diagnostics: Vec::new(),
		types: vec![
			// Order MUST match the IDX constants defined at the top of this file.
			Type::Error,
			Type::Infer,
			Type::Unit,
			Type::Never,
			Type::Integer,
			Type::Float,
			Type::U8,
			Type::I8,
			Type::U16,
			Type::I16,
			Type::U32,
			Type::I32,
			Type::U64,
			Type::I64,
			Type::F32,
			Type::F64,
			Type::Bool,
			Type::Char,
		],
		functions: Vec::new(),
		globals: Vec::new(),
		export_block: None,
		use_items: Vec::new(),
		use_prefixes: Vec::new(),
		namespaces: Vec::new(),
		package_namespaces: HashMap::new(),
		file_namespaces: vec![0; graph.files.len()],
		module_decls: Vec::new(),
		import_decls: Vec::new(),
		enums: Vec::new(),
		inherent_impls: Vec::new(),
		inherent_impl_dispatch: HashMap::new(),
		structs: Vec::new(),
		memories: Vec::new(),
		traits: Vec::new(),
		trait_impls: Vec::new(),
		trait_impl_dispatch: HashMap::new(),
		constants: Vec::new(),
		assoc_type_impls: Vec::new(),
		tagged_items: HashMap::new(),
		typesets: Vec::new(),
		type_aliases: Vec::new(),
		item_lookup: HashMap::new(),
	};
	let type_index_lookup = HashMap::from_iter(
		tir.types
			.iter()
			.enumerate()
			.map(|(idx, ty)| (ty.clone(), TypeIndex(idx as u32))),
	);
	let mut builder = Builder {
		interner: &mut graph.interner,
		id_generator: &mut graph.id_generator,
		files: &graph.files,
		packages: &graph.packages,
		root_package: graph.root_package,
		stdlib_package: graph.stdlib_package,
		tir,
		type_index_lookup,
		sig_state: HashMap::new(),
		ast_nodes: Vec::new(),
		operator_traits: None,
	};

	// Every package gets a root namespace of its own, the root package
	// included. That is what makes `parent: None` mean "nothing above this"
	// and nothing else — previously it also meant "the root package's own
	// scope", which is why a lookup walking past any package boundary fell
	// through into the root's items, and why `is_ancestor_or_self` needed a
	// hand-written stop at package roots.
	//
	// Created by walking `graph.packages` in order, so `NamespaceIndex`
	// values never depend on `HashMap` iteration order: they end up in
	// snapshots.
	for package_graph in &graph.packages {
		let namespace_idx = builder.tir.namespaces.len() as NamespaceIndex;
		builder.tir.namespaces.push(ModuleNamespace {
			parent: None,
			package: package_graph.id,
			declaration: ModuleDeclarationKind::Package(
				package_graph.modules[package_graph.root.as_usize()].file_id,
			),
			symbols: HashMap::new(),
			wildcard_imports: Vec::new(),
			accesses: Vec::new(),
		});
		builder
			.tir
			.package_namespaces
			.insert(package_graph.id, namespace_idx);
		// `crate` at a package root points at itself — there's no `super`
		// here, since `parent: None` is exactly what marks a package
		// boundary everywhere else in the resolver.
		let crate_sym = builder.interner.get_or_intern("crate");
		builder.tir.namespaces[namespace_idx as usize]
			.symbols
			.insert(
				(SymbolNamespace::Type, crate_sym),
				SymbolEntry::Resolved {
					kind: SymbolKind::Module { namespace_idx },
					visibility: Visibility::Public,
				},
			);
	}

	// A dependency is an implicit `mod <key>;` at the top of the declaring
	// package's entry file, so its name is an ordinary `Module` symbol in
	// that package's own namespace. Nothing global is involved, which is what
	// keeps a package's dependencies invisible to everyone else — including
	// to its own dependents, who never declared them.
	for package in &graph.packages {
		let owner = builder.tir.package_namespaces[&package.id];
		for (&name, target) in &package.dependencies {
			let target_namespace = builder.tir.package_namespaces[target];
			builder.tir.namespaces[owner as usize].symbols.insert(
				(SymbolNamespace::Type, name),
				SymbolEntry::Resolved {
					kind: SymbolKind::Module {
						namespace_idx: target_namespace,
					},
					visibility: Visibility::Public,
				},
			);
		}
	}

	// Phase 1a: one namespace per file, created directly from the
	// `SourceModule` tree vfs already built. `ModuleId`s are assigned in
	// push order and vfs always pushes a parent before loading any child,
	// so a child's `ModuleId` — and therefore its position in
	// `source_modules` — always comes after its parent's; a child's parent
	// namespace is therefore always already in `file_namespaces` by the
	// time the child is processed. Every field of every `ModuleDecl` is set
	// exactly once, here, straight from vfs's data — nothing downstream
	// ever writes to one afterward.
	for source_module in source_modules.iter().copied() {
		let package = &builder.packages[source_module.package_id.as_usize()];
		let namespace = match &source_module.declaration {
			None => builder.tir.package_namespaces[&package.id],
			Some(declaration) => {
				let parent_module =
					&package.modules[declaration.parent.as_usize()];
				let parent_namespace = builder.tir.file_namespaces
					[parent_module.file_id.as_usize()];
				match builder.check_module_collision(
					parent_module.file_id,
					parent_namespace,
					declaration.name,
				) {
					Some(existing) => existing,
					None => builder.create_module_namespace(
						parent_module.file_id,
						parent_namespace,
						declaration.name,
						declaration.pub_span,
						Some(source_module.file_id),
					),
				}
			}
		};
		builder.tir.file_namespaces[source_module.file_id.as_usize()] =
			namespace;
	}

	// Phase 1b: register all top-level items into ast_nodes / pending.
	for source_module in source_modules.iter().copied() {
		let namespace =
			builder.tir.file_namespaces[source_module.file_id.as_usize()];
		for item in source_module.ast.items.iter() {
			builder.pre_scan_item(
				source_module.file_id,
				namespace,
				&item.inner.inner,
			);
		}
	}

	// Build sig_state from ast_nodes with exact capacity; all start as Pending.
	builder.sig_state = HashMap::with_capacity(builder.ast_nodes.len());
	for (node_idx, entry) in builder.ast_nodes.iter().enumerate() {
		builder.sig_state.insert(
			entry.def_id,
			SigEntry {
				node_idx,
				state: ComputeState::Pending,
			},
		);
	}

	// Phase 2: demand-resolve signatures in parse order (vec is already ordered).
	for i in 0..builder.ast_nodes.len() {
		builder.ensure_signature(builder.ast_nodes[i].def_id);
	}

	builder.operator_traits = Some(builder.resolve_operator_traits());

	// Phase 3: demand-resolve bodies in parse order.
	for i in 0..builder.ast_nodes.len() {
		builder.ensure_body(builder.ast_nodes[i].def_id);
	}

	// Phase 3.5: verify every trait impl provides all required items
	builder.check_trait_conformance();

	builder.report_unused_items();

	// Nothing to hand over: top-level items and root wildcard imports now
	// live on each package's own namespace, already inside `builder.tir`.

	builder.tir
}

impl<'ast> Builder<'ast, '_> {
	/// Records a `Self` keyword usage against the impl block or trait impl
	/// it resolved through, into `self_accesses` — separate from the target
	/// type's own `accesses` (still recorded alongside this, in the caller)
	/// so LSP consumers can tell "literally named the type" apart from
	/// "used the `Self` keyword". `owner` is `scope.owner` at the point
	/// `Self` was resolved: the container directly for impl bodies (impl
	/// consts, impl block header bounds), or `Function` for method
	/// signatures/bodies — walked one hop via `type_param_parent` the same
	/// way `own_params` lookup already does for user-declared type params.
	fn record_self_keyword_access(
		&mut self,
		owner: TypeParamOwner,
		span: SourceSpan,
	) {
		let container = match owner {
			TypeParamOwner::ImplBlock(_) | TypeParamOwner::TraitImpl(_) => {
				Some(owner)
			}
			TypeParamOwner::Function(id) => {
				self.tir.function_index(id).and_then(|idx| {
					self.tir.functions[idx as usize].type_param_parent
				})
			}
			_ => None,
		};
		match container {
			Some(TypeParamOwner::ImplBlock(idx)) => {
				self.tir.inherent_impls[idx as usize]
					.self_accesses
					.push(span);
			}
			Some(TypeParamOwner::TraitImpl(idx)) => {
				self.tir.trait_impls[idx as usize].self_accesses.push(span);
			}
			_ => {}
		}
	}

	fn report_unused_items(&mut self) {
		let code = DiagnosticCode::UnusedItem.code();
		let type_param_code = DiagnosticCode::UnusedTypeParam.code();

		for function in self.tir.functions.iter() {
			let is_intrinsic =
				function.attributes.contains(&ItemAttribute::Intrinsic);
			let is_imported = matches!(
				self.tir.namespaces[function.namespace as usize].declaration,
				ModuleDeclarationKind::Import(_)
			);
			if is_intrinsic || is_imported {
				continue;
			}
			// Trait impl methods/associated functions are never flagged as
			// dead code, matching Rust: implementing a trait is itself the
			// "use" — the method exists to satisfy the trait's contract
			// (and may be invoked by generic code the compiler can't
			// statically trace back to this particular impl), regardless
			// of whether any accesses were ever recorded against it.
			// `type_param_parent` already distinguishes this for free:
			// `TraitImpl(_)` is only ever set by `AstNodeRef::TraitImplFunction`,
			// never by the inherent-impl path (`ImplBlock(_)`). Inherent
			// methods get no such exemption.
			if function.accesses.is_empty()
				&& function.pub_span.is_none()
				&& !matches!(
					function.type_param_parent,
					Some(
						TypeParamOwner::Trait(_) | TypeParamOwner::TraitImpl(_)
					)
				) {
				let name = self.interner.resolve(function.name.inner).unwrap();
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(code)
						.with_message(format!(
							"function `{}` is never used",
							name
						))
						.with_label(
							SourceSpan::new(
								function.file_id,
								function.name.span,
							)
							.primary_label(),
						),
				);
			}

			for param in function.type_params.iter() {
				if param.accesses.is_empty() {
					let name = self.interner.resolve(param.name.inner).unwrap();
					self.tir.diagnostics.push(
						Diagnostic::warning()
							.with_code(type_param_code)
							.with_message(format!(
								"type parameter `{name}` is never used"
							))
							.with_label(
								SourceSpan::new(
									function.file_id,
									param.name.span,
								)
								.primary_label(),
							)
							.with_note(
								"consider removing this type parameter or using it in signature",
							),
					);
				}
			}
		}

		for global in self.tir.globals.iter() {
			let is_imported = matches!(
				self.tir.namespaces[global.namespace as usize].declaration,
				ModuleDeclarationKind::Import(_)
			);
			if !is_imported && global.accesses.is_empty() {
				let name = self.interner.resolve(global.name.inner).unwrap();
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(code)
						.with_message(format!(
							"global variable `{}` is never used",
							name
						))
						.with_label(
							SourceSpan::new(global.file_id, global.name.span)
								.primary_label(),
						),
				);
			}
		}

		for constant in self.tir.constants.iter() {
			// A trait const's default value (`parent: Some(ItemParent::Trait(_))`)
			// is exempt for the same reason a default trait method is (see
			// above): the trait declaration is itself the "use" — the
			// default exists for whatever impl/generic code inherits it,
			// which the compiler can't statically trace back here. Trait
			// consts always carry `pub_span: None` (visibility comes from
			// the trait, not the item), so without this they'd all read as
			// "private and unused" the moment they got a default value —
			// previously unreachable, since every trait const was bodiless.
			if constant.pub_span.is_none()
				&& constant.accesses.is_empty()
				&& constant.value.is_some()
				&& !matches!(constant.parent, Some(ItemParent::Trait(_)))
			{
				let name = self.interner.resolve(constant.name.inner).unwrap();
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(code)
						.with_message(format!("const `{}` is never used", name))
						.with_label(
							SourceSpan::new(
								constant.file_id,
								constant.name.span,
							)
							.primary_label(),
						),
				);
			}
		}

		let field_code = DiagnosticCode::UnusedStructField.code();

		for struct_ in self.tir.structs.iter() {
			if struct_.pub_span.is_none() && struct_.accesses.is_empty() {
				let name = self.interner.resolve(struct_.name.inner).unwrap();
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(code)
						.with_message(format!(
							"struct `{}` is never used",
							name
						))
						.with_label(
							SourceSpan::new(struct_.file_id, struct_.name.span)
								.primary_label(),
						),
				);
			} else {
				// Struct is live — warn about fields that are initialized but never read.
				for field in struct_.fields.iter() {
					if field.pub_span.is_some() {
						continue;
					}
					let has_read = field.accesses.iter().any(|a| {
						matches!(
							a.kind,
							FieldAccessKind::Read | FieldAccessKind::ReadWrite
						)
					});
					let has_init = field
						.accesses
						.iter()
						.any(|a| matches!(a.kind, FieldAccessKind::Init));
					if has_init && !has_read {
						let name =
							self.interner.resolve(field.name.inner).unwrap();
						self.tir.diagnostics.push(
							Diagnostic::warning()
								.with_code(field_code)
								.with_message(format!(
									"field `{name}` is never read"
								))
								.with_label(
									SourceSpan::new(
										struct_.file_id,
										field.name.span,
									)
									.primary_label(),
								),
						);
					}
				}
			}
		}

		for enum_index in 0..self.tir.enums.len() as EnumIndex {
			let enum_ = &self.tir.enums[enum_index as usize];
			if enum_.pub_span.is_none() && enum_.accesses.is_empty() {
				let name = self.interner.resolve(enum_.name.inner).unwrap();
				self.tir.diagnostics.push(
					Diagnostic::warning()
						.with_code(code)
						.with_message(format!("enum `{}` is never used", name))
						.with_label(
							SourceSpan::new(enum_.file_id, enum_.name.span)
								.primary_label(),
						),
				);
				continue;
			}

			let unused_variants: Box<_> = enum_
				.variants
				.iter()
				.filter(|v| v.accesses.is_empty())
				.map(|v| v.name)
				.collect();
			if unused_variants.is_empty() {
				continue;
			}
			let diagnostic = report_unused_enum_variants(
				self.interner,
				enum_.file_id,
				&unused_variants,
			);
			self.tir.diagnostics.push(diagnostic);
		}
	}
}
