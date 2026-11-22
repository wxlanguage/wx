//! Hover text, rendered here from the compiler's resolved names and tables.
//!
//! The compiler records what a name means (`query::symbol_at` reads it) and
//! exposes its declarations, signatures and type formatter; everything about
//! how that reads on screen is decided in this module.

use string_interner::symbol::SymbolU32;
use wx_compiler::ast::{ExprId, Expression};
use wx_compiler::ast::{Keyword, Spanned, StringInterner};
use wx_compiler::diagnostics::{SourceSpan, TextOffset};
use wx_compiler::tir::{
	AssocTypeIdx, Body, BodyOwner, ConstIdx, ConstScalar, DeclKind, Definition,
	FieldIdx, FieldOwner, FunctionIdx, GenericEnvIdx, GenericEnvOwner,
	MemberKind, MemberOwner, Reference, ScopeIdx, Semantics, StructIdx,
	TargetIdx, Type, TypeIndex, TypesetIdx, Val, Visibility,
};
use wx_compiler::vfs::{FileId, Files};

use crate::snapshot::Snapshot;

/// A definition's signature as `wx` source; its owner is separate context.
pub(crate) fn signature(
	sema: &Semantics,
	strings: &StringInterner,
	definition: Definition,
) -> Option<String> {
	let renderer = Renderer { sema, strings };
	match definition {
		Definition::Item(key) => match sema.declaration_kind(key) {
			DeclKind::Function(function) => Some(renderer.function(function)),
			DeclKind::Struct(index) => Some(renderer.structure(index)),
			DeclKind::Enum(index) => Some(renderer.enumeration(index)),
			DeclKind::Const(index) => {
				let constant = &sema.decls.constants[usize::from(index)];
				let signature = &sema.constants[usize::from(index)];
				Some(format!(
					"const {}: {}",
					renderer.name(sema.decls.item(constant.loc).name),
					renderer.ty(signature.ty)
				))
			}
			DeclKind::TypeAlias(index) => {
				let alias = &sema.decls.type_aliases[usize::from(index)];
				let signature = &sema.type_aliases[usize::from(index)];
				let name = renderer.name(sema.decls.item(alias.loc).name);
				let target = renderer.ty(signature.target);
				// A primitive is declared without a body and names
				// itself, which `type i32 = i32` would read as a loop.
				if target == name {
					return Some(format!("type {name}"));
				}
				Some(format!(
					"type {name}{} = {target}",
					renderer.type_params(signature.type_params),
				))
			}
			DeclKind::EnumVariant(index) => renderer.variant(index),
			DeclKind::Trait(index) => {
				let decl = &sema.decls.traits[usize::from(index)];
				let name = renderer.name(sema.decls.item(decl.loc).name);
				Some(renderer.bounded(format!("trait {name}"), definition))
			}
			DeclKind::TypeSet(index) => {
				Some(renderer.typeset(index, definition))
			}
			DeclKind::Memory(index) => {
				let decl = &sema.decls.memories[usize::from(index)];
				let size = sema.assoc_types
					[usize::from(decl.size_assoc_type_index)]
				.as_ref()?
				.value?;
				Some(format!(
					"memory {}: {}",
					renderer.name(sema.decls.item(decl.loc).name),
					renderer.ty(size)
				))
			}
			DeclKind::Global(index) => {
				let decl = &sema.decls.globals[usize::from(index)];
				let value = sema.assoc_types
					[usize::from(decl.value_assoc_type_index)]
				.as_ref()?
				.value?;
				let mutable = if decl.mut_trait_impl_index.is_some() {
					"mut "
				} else {
					""
				};
				Some(format!(
					"global {mutable}{}: {}",
					renderer.name(sema.decls.item(decl.loc).name),
					renderer.ty(value)
				))
			}
			DeclKind::AssocType(index) => Some(renderer.associated_type(index)),
			DeclKind::Import(index) => {
				let decl = &sema.decls.imports[usize::from(index)];
				Some(format!(
					"import \"{}\" as {}",
					renderer.name(decl.external_name),
					renderer.name(sema.decls.item(decl.loc).name)
				))
			}
			DeclKind::Module(index) => {
				let decl = &sema.decls.modules[usize::from(index)];
				Some(format!(
					"mod {}",
					renderer.name(sema.decls.item(decl.loc).name)
				))
			}
			// Named by no name of its own, only by the key each dependent
			// declares it under; `documentation` says where its source is.
			DeclKind::Package(_) => Some("package".to_owned()),
			DeclKind::PackageInstance(index) => {
				let decl = &sema.decls.namespaces.package_instances()
					[usize::from(index)];
				Some(format!(
					"package \"{}\" as {}",
					renderer.name(decl.package_name),
					renderer.name(sema.decls.item(decl.loc).name)
				))
			}
		},
		Definition::TypeParam { env, index } => {
			let names = sema.generic_envs.param_names(env);
			let name = names.get(index as usize)?;
			let head = format!("type {}", renderer.name(*name));
			Some(renderer.bounded(head, definition))
		}
		Definition::Member(MemberKind::Function(function))
		| Definition::Member(MemberKind::Method(function)) => {
			Some(renderer.function(function))
		}
		Definition::Member(MemberKind::AssociatedType(index)) => {
			Some(renderer.associated_type(index))
		}
		Definition::Member(MemberKind::Constant(index)) => {
			let constant = &sema.decls.constants[usize::from(index)];
			let signature = &sema.constants[usize::from(index)];
			Some(format!(
				"const {}: {}",
				renderer.name(sema.decls.item(constant.loc).name),
				renderer.ty(signature.ty)
			))
		}
		Definition::InherentImplTarget(index) => {
			let header = sema.inherent_impls[usize::from(index)].as_ref()?;
			Some(format!("type Self = {}", renderer.ty(header.target.inner)))
		}
		Definition::TraitImplTarget(index) => {
			let header = sema.trait_impls[usize::from(index)].as_ref()?;
			Some(format!("type Self = {}", renderer.ty(header.target.inner)))
		}
		Definition::Label { .. } => None,
		Definition::JumpTarget { owner, target } => {
			renderer.jump_target(owner, target)
		}
		Definition::FunctionBody(function) => signature(
			sema,
			strings,
			Definition::Item(sema.decls.functions[usize::from(function)].loc),
		),
		Definition::Local { owner, local } => {
			let body = sema.owner_body(owner)?;
			let local_data = body.local(local);
			let is_parameter = body.params().contains(&Some(local));
			let mutable = if local_data.mut_span.is_some() {
				"mut "
			} else {
				""
			};
			let prefix = if is_parameter { "" } else { "local " };
			Some(format!(
				"{prefix}{mutable}{}: {}",
				renderer.name(local_data.name),
				renderer.ty(local_data.ty)
			))
		}
		Definition::Field { owner, field } => renderer.field(owner, field),
		Definition::Parameter {
			function,
			parameter,
		} => renderer.parameter(function, usize::from(parameter)),
	}
}

/// The signature of the `break`, `continue` or `return` `reference` is:
/// the values it takes, which its target gives, and `!`, since it never
/// falls through. `None` for any other reference.
pub(crate) fn jump(
	sema: &Semantics,
	strings: &StringInterner,
	reference: Reference,
) -> Option<String> {
	let renderer = Renderer { sema, strings };
	let (head, values) = match reference {
		Reference::Break { owner, target } => {
			let body = sema.owner_body(owner)?;
			let head = renderer.labelled(Keyword::Break, body, target);
			(head, renderer.values(body.target_type(target)))
		}
		Reference::Continue { owner, target } => {
			let body = sema.owner_body(owner)?;
			let head = renderer.labelled(Keyword::Continue, body, target);
			(head, renderer.loop_params(body, body.target_scope(target)))
		}
		Reference::Return { function } => {
			let result = sema.functions[usize::from(function)].return_type;
			(Keyword::Return.as_str().to_owned(), renderer.values(result))
		}
		_ => return None,
	};
	Some(renderer.arrow(&head, &values, TypeIndex::NEVER))
}

/// The signature of the `if` or `match` whose keyword is written at
/// `offset`: the value it branches on and the value its branches give,
/// with the keyword's span.
pub(crate) fn branch(
	snapshot: &Snapshot,
	file: FileId,
	offset: TextOffset,
) -> Option<(SourceSpan, String)> {
	let ast = snapshot.compilation.ast(file);
	let (expr, keyword, on) = (0..ast.exprs.kinds.len())
		.map(|index| ExprId(index as u32))
		.filter_map(|expr| match ast.expr(expr) {
			Expression::IfElse { condition, .. } => {
				Some((expr, Keyword::If, condition))
			}
			Expression::Match { scrutinee, .. } => {
				Some((expr, Keyword::Match, scrutinee))
			}
			_ => None,
		})
		.find(|&(expr, keyword, _)| {
			let span = keyword.span_at(ast.expr_span(expr).start);
			span.start <= offset && offset <= span.end
		})?;
	let owner = snapshot.expression_owner(file, expr)?;
	let body = snapshot.sema.owner_body(owner)?;
	let ty = |expr| Some(body.operand_ty(body.operand_of(ast, expr)?));
	let renderer = Renderer {
		sema: &snapshot.sema,
		strings: &snapshot.strings,
	};
	let span = keyword.span_at(ast.expr_span(expr).start);
	Some((
		SourceSpan::new(file, span),
		renderer.arrow(keyword.as_str(), &renderer.values(ty(on)?), ty(expr)?),
	))
}

/// A compact callable type for a completion's right-hand description. The
/// name is already in its label; only `self` keeps its parameter name.
pub(crate) fn callable_type(
	sema: &Semantics,
	strings: &StringInterner,
	definition: Definition,
) -> Option<String> {
	let renderer = Renderer { sema, strings };
	let function = match definition {
		Definition::Member(
			MemberKind::Function(function) | MemberKind::Method(function),
		) => function,
		Definition::Item(loc) => match sema.declaration_kind(loc) {
			DeclKind::Function(function) => function,
			DeclKind::Struct(index) => {
				let decl = &sema.decls.structs[usize::from(index)];
				let signature = &sema.structs[usize::from(index)];
				let fields = sema
					.types
					.list(signature.field_types)
					.iter()
					.map(|&ty| renderer.ty(ty))
					.collect::<Vec<_>>();
				return Some(format!(
					"func({}) -> {}{}",
					fields.join(", "),
					renderer.name(sema.decls.item(decl.loc).name),
					renderer.type_params(signature.type_params)
				));
			}
			_ => return None,
		},
		_ => return None,
	};
	let decl = &sema.decls.functions[usize::from(function)];
	let signature = &sema.functions[usize::from(function)];
	let params = sema
		.types
		.list(signature.param_types)
		.iter()
		.zip(sema.decls.params.names(decl.params))
		.map(|(&ty, &name)| {
			let ty = renderer.ty(ty);
			if name == Some(Keyword::SelfLower.symbol()) {
				format!("self: {ty}")
			} else {
				ty
			}
		})
		.collect::<Vec<_>>();
	Some(format!(
		"func({}) -> {}",
		params.join(", "),
		renderer.ty(signature.return_type)
	))
}

/// The enclosing trait or impl, when a hovered function has one. Completion
/// already shows trait provenance beside its label and uses only the signature.
pub(crate) fn owner(
	sema: &Semantics,
	strings: &StringInterner,
	definition: Definition,
) -> Option<String> {
	let function = match definition {
		Definition::Item(loc) => match sema.declaration_kind(loc) {
			DeclKind::Function(function) => function,
			_ => return None,
		},
		Definition::Member(
			MemberKind::Function(function) | MemberKind::Method(function),
		) => function,
		_ => return None,
	};
	Renderer { sema, strings }
		.member_owner(sema.decls.functions[usize::from(function)].owner)
}

/// The one integer a constant's value holds, signed as its type reads it.
/// A narrow signed integer is held sign-extended.
fn integer(value: &[ConstScalar]) -> Option<i128> {
	let &[ConstScalar { val, scalar }] = value else {
		return None;
	};
	match (val, scalar.is_signed()) {
		(Val::I32(bits), true) => Some(i128::from(bits as i32)),
		(Val::I32(bits), false) => Some(i128::from(bits)),
		(Val::I64(bits), true) => Some(i128::from(bits as i64)),
		(Val::I64(bits), false) => Some(i128::from(bits)),
		_ => None,
	}
}

struct Renderer<'a> {
	sema: &'a Semantics,
	strings: &'a StringInterner,
}

impl Renderer<'_> {
	fn name(&self, name: Spanned<SymbolU32>) -> &str {
		self.symbol(name.inner)
	}

	fn symbol(&self, symbol: SymbolU32) -> &str {
		self.strings.resolve(symbol).unwrap_or("?")
	}

	fn ty(&self, ty: wx_compiler::tir::TypeIndex) -> String {
		self.sema.type_formatter(self.strings).display_type(ty)
	}

	/// The values a value of `ty` is on the stack, as a list: a tuple's
	/// elements, none for `()`, else the value itself.
	fn values(&self, ty: TypeIndex) -> String {
		match *self.sema.types.resolve(ty) {
			Type::Tuple { elements } => self
				.sema
				.types
				.list(elements)
				.iter()
				.map(|&element| self.ty(element))
				.collect::<Vec<_>>()
				.join(", "),
			_ => self.ty(ty),
		}
	}

	/// `head(inputs) -> output`: what a construct takes and what it gives.
	fn arrow(&self, head: &str, inputs: &str, output: TypeIndex) -> String {
		format!("{head}({inputs}) -> {}", self.ty(output))
	}

	/// `keyword :label`, with the label of `target`, if it has one.
	fn labelled(
		&self,
		keyword: Keyword,
		body: &Body,
		target: TargetIdx,
	) -> String {
		match body.target(target).label {
			Some(label) => {
				format!("{} :{}", keyword.as_str(), self.name(label))
			}
			None => keyword.as_str().to_owned(),
		}
	}

	/// A loop's parameters, the locals `scope` declares, as a parameter
	/// list.
	fn loop_params(&self, body: &Body, scope: ScopeIdx) -> String {
		body.scope_locals(scope)
			.map(|param| {
				let local = body.local(param);
				let mutable =
					if local.mut_span.is_some() { "mut " } else { "" };
				format!(
					"{mutable}{}: {}",
					self.name(local.name),
					self.ty(local.ty)
				)
			})
			.collect::<Vec<_>>()
			.join(", ")
	}

	/// A loop's or a `block`'s signature: its parameters, none for a
	/// `block`, and the type of the value leaving it gives.
	fn jump_target(
		&self,
		owner: BodyOwner,
		target: TargetIdx,
	) -> Option<String> {
		let body = self.sema.owner_body(owner)?;
		let head =
			self.labelled(body.target_kind(target).keyword(), body, target);
		let params = self.loop_params(body, body.target_scope(target));
		Some(self.arrow(&head, &params, body.target_type(target)))
	}

	/// `<A, B>`, or nothing when the declaration has no parameters of its own.
	fn type_params(&self, env: GenericEnvIdx) -> String {
		let names = self.sema.generic_envs.param_names(env);
		if names.is_empty() {
			return String::new();
		}
		let params: Vec<_> = (names.iter().enumerate())
			.map(|(index, name)| {
				let index = index as u32;
				let head = self.name(*name).to_string();
				self.bounded(head, Definition::TypeParam { env, index })
			})
			.collect();
		format!("<{}>", params.join(", "))
	}

	/// `head`, followed by the bounds written on `definition`, if any. A
	/// trait's own `Self` is bounded by the trait itself.
	fn bounded(&self, head: String, definition: Definition) -> String {
		if let Definition::TypeParam { env, index: 0 } = definition
			&& let GenericEnvOwner::Trait(trait_index) =
				self.sema.generic_envs.owner(env)
		{
			let name = self.name(self.sema.decls.name(trait_index));
			return format!("{head}: {name}");
		}
		let bounds = self.sema.written_bounds(definition);
		let bounds =
			(self.sema.bound_formatter(self.strings)).display_bounds(&bounds);
		if bounds.is_empty() {
			head
		} else {
			format!("{head}: {bounds}")
		}
	}

	/// `typeset Name: Bounds { A, B }`: its bounds and its members.
	fn typeset(&self, index: TypesetIdx, definition: Definition) -> String {
		let decl = &self.sema.decls.typesets[usize::from(index)];
		let name = self.name(self.sema.decls.item(decl.loc).name);
		let members: Vec<_> = (decl.member_impls.iter())
			.filter_map(|&member| {
				let header =
					self.sema.trait_impls[usize::from(member)].as_ref()?;
				Some(self.ty(header.target.inner))
			})
			.collect();
		format!(
			"{} {{ {} }}",
			self.bounded(format!("typeset {name}"), definition),
			members.join(", ")
		)
	}

	/// The function's own parameter frame, or the empty root frame when its
	/// signature uses an enclosing impl's or trait's frame instead.
	fn own_type_params(&self, function: FunctionIdx) -> GenericEnvIdx {
		let env = self.sema.functions[usize::from(function)].type_params;
		if env != GenericEnvIdx::ROOT
			&& self.sema.generic_envs.owner(env)
				== GenericEnvOwner::Function(function)
		{
			env
		} else {
			GenericEnvIdx::ROOT
		}
	}

	fn function(&self, function: FunctionIdx) -> String {
		let decl = &self.sema.decls.functions[usize::from(function)];
		let signature = &self.sema.functions[usize::from(function)];
		let types = self.sema.types.list(signature.param_types);
		let params: Vec<_> = types
			.iter()
			.zip(self.sema.decls.params.names(decl.params))
			.map(|(ty, name)| match name {
				Some(name) => {
					format!("{}: {}", self.symbol(*name), self.ty(*ty))
				}
				None => self.ty(*ty),
			})
			.collect();
		format!(
			"func {}{}({}) -> {}",
			self.name(self.sema.decls.item(decl.loc).name),
			self.type_params(self.own_type_params(function)),
			params.join(", "),
			self.ty(signature.return_type)
		)
	}

	fn member_owner(&self, owner: MemberOwner) -> Option<String> {
		match owner {
			MemberOwner::Free => None,
			MemberOwner::Trait(index) => {
				let decl = &self.sema.decls.traits[usize::from(index)];
				Some(format!(
					"trait {}",
					self.name(self.sema.decls.item(decl.loc).name)
				))
			}
			MemberOwner::InherentImpl(index) => {
				let header =
					self.sema.inherent_impls[usize::from(index)].as_ref()?;
				Some(format!(
					"impl{} {}",
					self.type_params(header.type_params),
					self.ty(header.target.inner),
				))
			}
			MemberOwner::TraitImpl(index) => {
				let header =
					self.sema.trait_impls[usize::from(index)].as_ref()?;
				let trait_index = self.sema.trait_impl_trait(index)?;
				let decl = &self.sema.decls.traits[usize::from(trait_index)];
				Some(format!(
					"impl{} {} for {}",
					self.type_params(header.type_params),
					self.name(self.sema.decls.item(decl.loc).name),
					self.ty(header.target.inner),
				))
			}
		}
	}

	fn structure(&self, index: StructIdx) -> String {
		let decl = &self.sema.decls.structs[usize::from(index)];
		let signature = &self.sema.structs[usize::from(index)];
		let types = self.sema.types.list(signature.field_types);
		let fields: Vec<_> = types
			.iter()
			.enumerate()
			.map(|(at, &ty)| {
				self.field_declaration(
					FieldOwner::Struct(index),
					FieldIdx::new(at as u32),
					ty,
				)
			})
			.collect();
		format!(
			"struct {}{}({})",
			self.name(self.sema.decls.item(decl.loc).name),
			self.type_params(signature.type_params),
			fields.join(", ")
		)
	}

	fn enumeration(&self, index: wx_compiler::tir::EnumIdx) -> String {
		let decl = &self.sema.decls.enums[usize::from(index)];
		let signature = &self.sema.enums[usize::from(index)];
		// The repr as its field is written, `value: u8`; a wider repr is not
		// supported, so its first field is all there is.
		let repr = match decl.fields.is_empty() {
			true => self.ty(signature.repr),
			false => self.field_declaration(
				FieldOwner::Enum(index),
				FieldIdx::new(0),
				signature.repr,
			),
		};
		format!(
			"enum {}({repr}) {{ .. }}",
			self.name(self.sema.decls.item(decl.loc).name),
		)
	}

	/// `type Name: Bounds = Value`: a declaration's bounds and default, or
	/// an impl's value.
	fn associated_type(&self, index: AssocTypeIdx) -> String {
		let decl = &self.sema.decls.assoc_types[usize::from(index)];
		let name = self.name(self.sema.decls.item(decl.loc).name);
		let head = self.bounded(
			format!("type {name}"),
			Definition::Member(MemberKind::AssociatedType(index)),
		);
		match self.sema.assoc_types[usize::from(index)]
			.as_ref()
			.and_then(|signature| signature.value)
		{
			Some(value) => format!("{head} = {}", self.ty(value)),
			None => head,
		}
	}

	/// `Enum::Variant = value`, the value the variant has in the enum's repr.
	fn variant(&self, index: ConstIdx) -> Option<String> {
		let variant = &self.sema.decls.constants[usize::from(index)];
		let &Type::Enum { enum_index } = self
			.sema
			.types
			.resolve(self.sema.constants[usize::from(index)].ty)
		else {
			return None;
		};
		let enum_decl = &self.sema.decls.enums[usize::from(enum_index)];
		let value = integer(self.sema.constant_value(index)?)?;
		Some(format!(
			"{}::{} = {value}",
			self.name(self.sema.decls.item(enum_decl.loc).name),
			self.name(self.sema.decls.item(variant.loc).name),
		))
	}

	fn field(&self, owner: FieldOwner, field: FieldIdx) -> Option<String> {
		let types = match owner {
			FieldOwner::Struct(index) => {
				self.sema.structs[usize::from(index)].field_types
			}
			FieldOwner::Enum(index) => {
				self.sema.enums[usize::from(index)].field_types
			}
		};
		let ty = *self.sema.types.list(types).get(usize::from(field))?;
		self.sema
			.decls
			.fields
			.name(owner.fields(&self.sema.decls), field)?;
		Some(self.field_declaration(owner, field, ty))
	}

	/// A field as it is declared, `pub mut name: Type`; its type alone when
	/// it has no name.
	fn field_declaration(
		&self,
		owner: FieldOwner,
		field: FieldIdx,
		ty: TypeIndex,
	) -> String {
		let fields = owner.fields(&self.sema.decls);
		let arena = &self.sema.decls.fields;
		let Some(name) = arena.name(fields, field) else {
			return self.ty(ty);
		};
		let public = match arena.visibility(fields)[usize::from(field)] {
			Visibility::Public => "pub ",
			Visibility::Private => "",
		};
		let mutable = match arena.mut_span(fields, field) {
			Some(_) => "mut ",
			None => "",
		};
		format!("{public}{mutable}{}: {}", self.symbol(name), self.ty(ty))
	}

	fn parameter(
		&self,
		function: FunctionIdx,
		parameter: usize,
	) -> Option<String> {
		let decl = &self.sema.decls.functions[usize::from(function)];
		let signature = &self.sema.functions[usize::from(function)];
		let ty = self.sema.types.list(signature.param_types).get(parameter)?;
		let name = self
			.sema
			.decls
			.params
			.names(decl.params)
			.get(parameter)
			.copied()??;
		Some(format!("{}: {}", self.symbol(name), self.ty(*ty)))
	}
}

/// Documentation attached to a definition, read from its own source file.
/// Parameters, fields and type parameters share their owner's line, where
/// the owner's comment must not be mistaken for their own documentation.
pub(crate) fn documentation(
	sema: &Semantics,
	files: &Files,
	definition: Definition,
) -> Option<String> {
	if !matches!(definition, Definition::Item(_) | Definition::Member(_)) {
		return None;
	}
	let span = sema.definition_span(definition)?;
	let file = files.get(span.file_id).ok()?;
	// A package is declared at the start of its entry file, which is what
	// describes it.
	if let Definition::Item(key) = definition
		&& let DeclKind::Package(_) = sema.declaration_kind(key)
	{
		return Some(format!("`{}`", file.name));
	}
	leading_doc_comment(&file.source, span.span.start)
}

/// The `///` lines directly above the declaration whose name is written at
/// `name_offset`, skipping attribute lines between them.
pub(crate) fn leading_doc_comment(
	source: &str,
	name_offset: TextOffset,
) -> Option<String> {
	let mut doc_lines = Vec::new();
	let mut line_start = source[..usize::from(name_offset)]
		.rfind('\n')
		.map_or(0, |i| i + 1);
	while line_start > 0 {
		let previous_start =
			source[..line_start - 1].rfind('\n').map_or(0, |i| i + 1);
		let line = source[previous_start..line_start - 1].trim();
		if let Some(text) = line.strip_prefix("///") {
			doc_lines.push(text.strip_prefix(' ').unwrap_or(text));
		} else if !line.starts_with("#[") {
			break;
		}
		line_start = previous_start;
	}
	if doc_lines.is_empty() {
		return None;
	}
	doc_lines.reverse();
	Some(doc_lines.join("\n"))
}
