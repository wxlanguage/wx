//! Renders definitions, and the control-flow constructs that have
//! signatures of their own, as `wx` source: what a declaration reads as
//! where it is written, or the compact form a list of them shows.
//!
//! Built on [`TypeFormatter`] and [`BoundFormatter`]; a definition's owner
//! (its trait or impl) is rendered separately, so a caller decides whether
//! to show it.

use string_interner::symbol::SymbolU32;

use crate::ast::{Keyword, Spanned, StringInterner};
use crate::tir::{
	AssocTypeIdx, Body, BodyOwner, ConstIdx, ConstScalar, DeclKind, Definition,
	EnumIdx, FieldIdx, FieldOwner, FunctionIdx, GenericFrameIdx,
	GenericFrameOwner, ItemPath, MemberKind, MemberOwner, Reference, ScopeIdx,
	Semantics, StructIdx, TargetIdx, Type, TypeIndex, TypesetIdx, Val,
	Visibility,
};

pub struct DefinitionFormatter<'a> {
	sema: &'a Semantics,
	strings: &'a StringInterner,
}

impl Semantics {
	pub fn definition_formatter<'a>(
		&'a self,
		strings: &'a StringInterner,
	) -> DefinitionFormatter<'a> {
		DefinitionFormatter {
			sema: self,
			strings,
		}
	}
}

impl DefinitionFormatter<'_> {
	/// A definition's signature as `wx` source; its owner is separate context.
	pub fn signature(&self, definition: Definition) -> Option<String> {
		let sema = self.sema;
		match definition {
			Definition::Item(key) => match sema.declaration_kind(key) {
				DeclKind::Function(function) => Some(self.function(function)),
				DeclKind::Struct(index) => Some(self.structure(index)),
				DeclKind::Enum(index) => Some(self.enumeration(index)),
				DeclKind::Const(index) => {
					let constant = &sema.decls.constants[usize::from(index)];
					let signature = &sema.constants[usize::from(index)];
					Some(format!(
						"const {}: {}",
						self.name(sema.decls.item(constant.loc).name),
						self.ty(signature.ty)
					))
				}
				DeclKind::TypeAlias(index) => {
					let alias = &sema.decls.type_aliases[usize::from(index)];
					let signature = &sema.type_aliases[usize::from(index)];
					let name = self.name(sema.decls.item(alias.loc).name);
					let target = self.ty(signature.target);
					// A primitive is declared without a body and names
					// itself, which `type i32 = i32` would read as a loop.
					if target == name {
						return Some(format!("type {name}"));
					}
					Some(format!(
						"type {name}{} = {target}",
						self.generic_params(signature.generic_params),
					))
				}
				DeclKind::EnumVariant(index) => self.variant(index),
				DeclKind::Trait(index) => {
					let decl = &sema.decls.traits[usize::from(index)];
					let name = self.name(sema.decls.item(decl.loc).name);
					Some(self.bounded(format!("trait {name}"), definition))
				}
				DeclKind::TypeSet(index) => {
					Some(self.typeset(index, definition))
				}
				DeclKind::Memory(index) => {
					let decl = &sema.decls.memories[usize::from(index)];
					let size = sema.assoc_types
						[usize::from(decl.size_assoc_type_index)]
					.as_ref()?
					.value?;
					Some(format!(
						"memory {}: {}",
						self.name(sema.decls.item(decl.loc).name),
						self.ty(size)
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
						self.name(sema.decls.item(decl.loc).name),
						self.ty(value)
					))
				}
				DeclKind::AssocType(index) => Some(self.associated_type(index)),
				DeclKind::Import(index) => {
					let decl = &sema.decls.imports[usize::from(index)];
					Some(format!(
						"import \"{}\" as {}",
						self.name(decl.external_name),
						self.name(sema.decls.item(decl.loc).name)
					))
				}
				DeclKind::Module(index) => {
					let decl = &sema.decls.modules[usize::from(index)];
					Some(format!(
						"mod {}",
						self.name(sema.decls.item(decl.loc).name)
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
						self.name(decl.package_name),
						self.name(sema.decls.item(decl.loc).name)
					))
				}
			},
			Definition::TypeParam { frame, index } => {
				let names = sema.generic_frames.param_names(frame);
				let name = names.get(index as usize)?;
				let head = format!("type {}", self.name(*name));
				Some(self.bounded(head, definition))
			}
			Definition::Member(MemberKind::Function(function))
			| Definition::Member(MemberKind::Method(function)) => {
				Some(self.function(function))
			}
			Definition::Member(MemberKind::AssociatedType(index)) => {
				Some(self.associated_type(index))
			}
			Definition::Member(MemberKind::Constant(index)) => {
				let constant = &sema.decls.constants[usize::from(index)];
				let signature = &sema.constants[usize::from(index)];
				Some(format!(
					"const {}: {}",
					self.name(sema.decls.item(constant.loc).name),
					self.ty(signature.ty)
				))
			}
			Definition::InherentImplTarget(index) => {
				let header =
					sema.inherent_impls[usize::from(index)].as_ref()?;
				Some(format!("type Self = {}", self.ty(header.target.inner)))
			}
			Definition::TraitImplTarget(index) => {
				let header = sema.trait_impls[usize::from(index)].as_ref()?;
				Some(format!("type Self = {}", self.ty(header.target.inner)))
			}
			Definition::Label { .. } => None,
			Definition::JumpTarget { owner, target } => {
				self.jump_target(owner, target)
			}
			Definition::FunctionBody(function) => {
				self.signature(Definition::Item(
					sema.decls.functions[usize::from(function)].loc,
				))
			}
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
					self.name(local_data.name),
					self.ty(local_data.ty)
				))
			}
			Definition::Field { owner, field } => self.field(owner, field),
			Definition::Parameter {
				function,
				parameter,
			} => self.parameter(function, usize::from(parameter)),
		}
	}

	/// The signature of the `break`, `continue` or `return` `reference` is:
	/// the values it takes, which its target gives, and `!`, since it never
	/// falls through. `None` for any other reference.
	pub fn jump(&self, reference: Reference) -> Option<String> {
		let sema = self.sema;
		let (head, values) = match reference {
			Reference::Break { owner, target } => {
				let body = sema.owner_body(owner)?;
				let head = self.labelled(Keyword::Break, body, target);
				(head, self.values(body.target_type(target)))
			}
			Reference::Continue { owner, target } => {
				let body = sema.owner_body(owner)?;
				let head = self.labelled(Keyword::Continue, body, target);
				(head, self.loop_params(body, body.target_scope(target)))
			}
			Reference::Return { function } => {
				let result = sema.functions[usize::from(function)].return_type;
				(Keyword::Return.as_str().to_owned(), self.values(result))
			}
			_ => return None,
		};
		Some(self.arrow(&head, &values, TypeIndex::NEVER))
	}

	/// The signature of an `if` or a `match`: the value it branches on and
	/// the value its branches give.
	pub fn branch(
		&self,
		keyword: Keyword,
		on: TypeIndex,
		result: TypeIndex,
	) -> String {
		self.arrow(keyword.as_str(), &self.values(on), result)
	}

	/// A declaration's compact form, for a list of declarations: what the
	/// name declares, never a type, since a function's, a constructor's or a
	/// global's type is its own. Parameters are listed by type, and only
	/// `self` keeps its name; type parameters by name. `None` for a name that
	/// is a value (a local, a constant), which its type describes.
	pub fn summary(&self, definition: Definition) -> Option<String> {
		let sema = self.sema;
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
						.map(|&ty| self.ty(ty))
						.collect::<Vec<_>>();
					return Some(format!(
						"struct {}{}({})",
						self.name(sema.decls.item(decl.loc).name),
						self.generic_param_names(signature.generic_params),
						fields.join(", ")
					));
				}
				DeclKind::Global(_) | DeclKind::Memory(_) => {
					return self.signature(definition);
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
				let ty = self.ty(ty);
				if name == Some(Keyword::SelfLower.symbol()) {
					format!("self: {ty}")
				} else {
					ty
				}
			})
			.collect::<Vec<_>>();
		Some(format!(
			"func {}{}({}) -> {}",
			self.name(sema.decls.item(decl.loc).name),
			self.generic_param_names(self.own_generic_params(function)),
			params.join(", "),
			self.ty(signature.return_type)
		))
	}

	/// The names of `path`'s steps, joined by `::`: `shapes::Point::origin`.
	/// Its package is not named; a caller writes the prefix its view of the
	/// package gives it.
	pub fn path(&self, path: &ItemPath) -> String {
		(path.steps.iter())
			.map(|&step| self.name(self.sema.decls.item(step).name))
			.collect::<Vec<_>>()
			.join("::")
	}

	/// The trait or impl enclosing a member (a function, a constant or an
	/// associated type), as its header reads; `None` for anything free.
	pub fn owner(&self, definition: Definition) -> Option<String> {
		let decls = &self.sema.decls;
		let owner = match definition {
			Definition::Item(loc) => self.sema.member_owner(loc),
			Definition::Member(
				MemberKind::Function(index) | MemberKind::Method(index),
			) => decls.functions[usize::from(index)].owner,
			Definition::Member(MemberKind::Constant(index)) => {
				decls.constants[usize::from(index)].owner
			}
			Definition::Member(MemberKind::AssociatedType(index)) => {
				decls.assoc_types[usize::from(index)].owner
			}
			_ => return None,
		};
		self.member_owner(owner)
	}

	fn name(&self, name: Spanned<SymbolU32>) -> &str {
		self.symbol(name.inner)
	}

	fn symbol(&self, symbol: SymbolU32) -> &str {
		self.strings.resolve(symbol).unwrap_or("?")
	}

	fn ty(&self, ty: TypeIndex) -> String {
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
	/// `<T, U>`: the type parameters of `frame` by name, without their
	/// bounds; nothing when it has none.
	fn generic_param_names(&self, frame: GenericFrameIdx) -> String {
		let names = self.sema.generic_frames.param_names(frame);
		if names.is_empty() {
			return String::new();
		}
		let names: Vec<_> = names
			.iter()
			.map(|&name| self.name(name).to_string())
			.collect();
		format!("<{}>", names.join(", "))
	}

	fn generic_params(&self, frame: GenericFrameIdx) -> String {
		let names = self.sema.generic_frames.param_names(frame);
		if names.is_empty() {
			return String::new();
		}
		let params: Vec<_> = (names.iter().enumerate())
			.map(|(index, name)| {
				let index = index as u32;
				let head = self.name(*name).to_string();
				self.bounded(head, Definition::TypeParam { frame, index })
			})
			.collect();
		format!("<{}>", params.join(", "))
	}

	/// `head`, followed by the bounds written on `definition`, if any. A
	/// trait's own `Self` is bounded by the trait itself.
	fn bounded(&self, head: String, definition: Definition) -> String {
		if let Definition::TypeParam { frame, index: 0 } = definition
			&& let GenericFrameOwner::Trait(trait_index) =
				self.sema.generic_frames.owner(frame)
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
	fn own_generic_params(&self, function: FunctionIdx) -> GenericFrameIdx {
		let frame = self.sema.functions[usize::from(function)].generic_params;
		if frame != GenericFrameIdx::ROOT
			&& self.sema.generic_frames.owner(frame)
				== GenericFrameOwner::Function(function)
		{
			frame
		} else {
			GenericFrameIdx::ROOT
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
			self.generic_params(self.own_generic_params(function)),
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
					self.generic_params(header.generic_params),
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
					self.generic_params(header.generic_params),
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
			self.generic_params(signature.generic_params),
			fields.join(", ")
		)
	}

	fn enumeration(&self, index: EnumIdx) -> String {
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

#[cfg(test)]
mod tests {
	use super::*;
	use crate::testing::DiagnosticView;
	use crate::tir::signatures::tests::source_graph;

	/// A checked single-file package over the embedded core, and its
	/// interner.
	struct Checked {
		strings: StringInterner,
		sema: Semantics,
	}

	impl Checked {
		fn new(source: &str) -> Self {
			let mut strings = Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let sema = crate::tir::check(&graph, &mut strings);
			DiagnosticView::new("check", sema.diagnostics(), &graph.files)
				.assert_no_errors();
			Self { strings, sema }
		}

		fn formatter(&self) -> DefinitionFormatter<'_> {
			self.sema.definition_formatter(&self.strings)
		}

		/// The one declaration named `name`, a namespace's or an impl's.
		fn item(&self, name: &str) -> Definition {
			let symbol = self.strings.get(name).expect("a fixture name");
			let decls = &self.sema.decls;
			let functions = decls.functions.iter().map(|decl| decl.loc);
			// A free function is both a namespace's and the function table's.
			let mut found = Vec::new();
			for loc in decls.namespaces.keys().chain(functions) {
				if decls.item(loc).name.inner == symbol && !found.contains(&loc)
				{
					found.push(loc);
				}
			}
			let [loc] = found[..] else {
				panic!("expected one declaration named `{name}`");
			};
			Definition::Item(loc)
		}
	}

	#[test]
	fn a_function_reads_as_declared_and_summarizes_by_parameter_type() {
		let case = Checked::new(
			"func pick<T: Eq>(first: T, second: T) -> T { first }",
		);
		let pick = case.item("pick");
		assert_eq!(
			case.formatter().signature(pick).as_deref(),
			Some("func pick<T: Eq>(first: T, second: T) -> T")
		);
		assert_eq!(
			case.formatter().summary(pick).as_deref(),
			Some("func pick<T>(T, T) -> T")
		);
		assert_eq!(case.formatter().owner(pick), None);
	}

	#[test]
	fn a_struct_keeps_its_fields_visibility_and_mutability() {
		let case = Checked::new("struct Point(x: i32, pub mut y: i32);");
		let point = case.item("Point");
		assert_eq!(
			case.formatter().signature(point).as_deref(),
			Some("struct Point(x: i32, pub mut y: i32)")
		);
		assert_eq!(
			case.formatter().summary(point).as_deref(),
			Some("struct Point(i32, i32)")
		);
	}

	#[test]
	fn a_method_is_rendered_apart_from_its_impl() {
		let case = Checked::new(
			"struct Point(x: i32);\n\
			 impl Point {\n\
			     func horizontal(self: Self) -> i32 { self.x }\n\
			 }",
		);
		let horizontal = case.item("horizontal");
		assert_eq!(
			case.formatter().signature(horizontal).as_deref(),
			Some("func horizontal(self: Point) -> i32")
		);
		assert_eq!(
			case.formatter().owner(horizontal).as_deref(),
			Some("impl Point")
		);
	}

	#[test]
	fn an_associated_type_and_a_constant_name_their_trait_or_impl() {
		let case = Checked::new(
			"trait Sized2 {\n\
			     type Unit;\n\
			     const WIDTH: u32;\n\
			 }\n\
			 struct Meter(value: u32);\n\
			 impl Sized2 for Meter {\n\
			     type Unit = u32;\n\
			     const WIDTH: u32 = 4;\n\
			 }",
		);
		let decls = &case.sema.decls;
		let owners = |name: &str| {
			let symbol = case.strings.get(name).unwrap();
			let mut owners: Vec<_> = (decls.namespaces.keys())
				.filter(|&loc| decls.item(loc).name.inner == symbol)
				.filter_map(|loc| case.formatter().owner(Definition::Item(loc)))
				.collect();
			owners.sort();
			owners
		};
		assert_eq!(owners("Unit"), ["impl Sized2 for Meter", "trait Sized2"]);
		assert_eq!(owners("WIDTH"), ["impl Sized2 for Meter", "trait Sized2"]);
	}

	#[test]
	fn an_enum_variant_shows_its_value_in_the_repr() {
		let case = Checked::new("enum Kind(value: u8) { A = 0, B }");
		assert_eq!(
			case.formatter().signature(case.item("Kind")).as_deref(),
			Some("enum Kind(value: u8) { .. }")
		);
		assert_eq!(
			case.formatter().signature(case.item("B")).as_deref(),
			Some("Kind::B = 1")
		);
	}
}
