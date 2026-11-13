//! Hover text, rendered here from the compiler's resolved names and tables.
//!
//! The compiler answers what a name means (`Semantics::symbol_at`) and
//! exposes its declarations, signatures and type formatter; everything about
//! how that reads on screen is decided in this module.

use string_interner::symbol::SymbolU32;
use wx_compiler::ast::{Keyword, Spanned, StringInterner};
use wx_compiler::tir::{
	AssocTypeIdx, ConstIdx, ConstScalar, DeclKind, Definition, FieldIdx,
	FunctionIdx, GenericEnvIdx, MemberKind, MemberOwner, Semantics, StructIdx,
	Type, Val,
};
use wx_compiler::vfs::Files;

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
				Some(format!(
					"trait {}",
					renderer.name(sema.decls.item(decl.loc).name)
				))
			}
			DeclKind::TypeSet(index) => {
				let decl = &sema.decls.typesets[usize::from(index)];
				Some(format!(
					"typeset {}",
					renderer.name(sema.decls.item(decl.loc).name)
				))
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
			DeclKind::PackageInstance(index) => {
				let decl = &sema.decls.namespaces.package_instances()
					[usize::from(index)];
				Some(format!(
					"package \"{}\" as {}",
					renderer.name(decl.package_name),
					renderer.name(sema.decls.item(decl.loc).name)
				))
			}
			_ => None,
		},
		Definition::TypeParam { env, index } => {
			let names = sema.generic_envs.param_names(env);
			let name = names.get(index as usize)?;
			Some(format!("type {}", renderer.name(*name)))
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
		.zip(&decl.params)
		.map(|(&ty, name)| {
			let ty = renderer.ty(ty);
			if name
				.is_some_and(|name| name.inner == Keyword::SelfLower.symbol())
			{
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
		self.strings.resolve(name.inner).unwrap_or("?")
	}

	fn ty(&self, ty: wx_compiler::tir::TypeIndex) -> String {
		self.sema.type_formatter(self.strings).display_type(ty)
	}

	/// `<A, B>`, or nothing when the declaration has no parameters of its own.
	fn type_params(&self, env: GenericEnvIdx) -> String {
		let names = self.sema.generic_envs.param_names(env);
		if names.is_empty() {
			return String::new();
		}
		let mut result = String::from("<");
		use std::fmt::Write;
		for (i, name) in names.iter().enumerate() {
			if i > 0 {
				result.push_str(", ");
			}
			write!(result, "{}", self.name(*name)).unwrap();
		}
		result.push('>');
		result
	}

	fn function(&self, function: FunctionIdx) -> String {
		let decl = &self.sema.decls.functions[usize::from(function)];
		let signature = &self.sema.functions[usize::from(function)];
		let types = self.sema.types.list(signature.param_types);
		let params: Vec<_> = types
			.iter()
			.zip(decl.params.iter())
			.map(|(ty, name)| match name {
				Some(name) => format!("{}: {}", self.name(*name), self.ty(*ty)),
				None => self.ty(*ty),
			})
			.collect();
		format!(
			"func {}{}({}) -> {}",
			self.name(self.sema.decls.item(decl.loc).name),
			self.type_params(self.sema.function_own_type_params(function)),
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
			.zip(decl.field_names.iter())
			.map(|(ty, name)| match name {
				Some(name) => format!("{}: {}", self.name(*name), self.ty(*ty)),
				None => self.ty(*ty),
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
		format!(
			"enum {}({}) {{ .. }}",
			self.name(self.sema.decls.item(decl.loc).name),
			self.ty(signature.repr)
		)
	}

	fn associated_type(&self, index: AssocTypeIdx) -> String {
		let decl = &self.sema.decls.assoc_types[usize::from(index)];
		let name = self.name(self.sema.decls.item(decl.loc).name);
		match self.sema.assoc_types[usize::from(index)]
			.as_ref()
			.and_then(|signature| signature.value)
		{
			Some(value) => format!("type {name} = {}", self.ty(value)),
			None => format!("type {name}"),
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

	fn field(&self, owner: StructIdx, field: FieldIdx) -> Option<String> {
		let decl = &self.sema.decls.structs[usize::from(owner)];
		let signature = &self.sema.structs[usize::from(owner)];
		let ty = self
			.sema
			.types
			.list(signature.field_types)
			.get(usize::from(field))?;
		let name = decl.field_names.get(usize::from(field))?.as_ref()?;
		Some(format!("{}: {}", self.name(*name), self.ty(*ty)))
	}

	fn parameter(
		&self,
		function: FunctionIdx,
		parameter: usize,
	) -> Option<String> {
		let decl = &self.sema.decls.functions[usize::from(function)];
		let signature = &self.sema.functions[usize::from(function)];
		let ty = self.sema.types.list(signature.param_types).get(parameter)?;
		let name = decl.params.get(parameter)?.as_ref()?;
		Some(format!("{}: {}", self.name(*name), self.ty(*ty)))
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
	let source = &files.get(span.file_id).ok()?.source;
	leading_doc_comment(source, span.span.start)
}

/// The `///` lines directly above the declaration whose name is written at
/// `name_offset`, skipping attribute lines between them.
pub(crate) fn leading_doc_comment(
	source: &str,
	name_offset: u32,
) -> Option<String> {
	let mut doc_lines = Vec::new();
	let mut line_start = source[..name_offset as usize]
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
