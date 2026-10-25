//! Memory layout: where the bytes of a value sit in linear memory.
//!
//! A struct's or tuple's fields are placed one after another, each at the
//! next offset its alignment allows, and the whole is padded to its own
//! alignment, the largest of its fields'. They are placed in descending
//! alignment, which leaves the least padding (a stable sort, so fields of one
//! alignment keep their declaration order), or in declaration order for a
//! struct marked `#[fixed_order]`. A tuple is always sorted. A slice is its
//! address and then its length, and an address is as wide as its memory's
//! `Size`. Zero-sized values (`!`, a function item, a memory's or a global's
//! handle) take no bytes and have alignment 1.
//!
//! This is the one place layout is decided: constant evaluation reads and
//! writes allocations by it, and lowering places values by it. Offsets are
//! physical (where the bytes are) but indexed by declaration, as rustc's
//! `FieldsShape::Arbitrary` keeps them.
//!
//! Only aggregates are remembered. A struct or a tuple is keyed by its
//! normalized type, and only when that type is concrete, so the key needs no
//! scope. Its layout is stored once per distinct content, as rustc interns
//! its `LayoutData`: `Pair<u32, u8>` and `(u32, u8)` are two keys and one
//! layout. Anything else is a direct mapping and is never stored.

use std::hash::BuildHasher;

use hashbrown::HashTable;
use rustc_hash::{FxBuildHasher, FxHashMap};

use super::defs::{FieldOrder, StructIdx};
use super::signatures::TypeContext;
use super::solver::{Solver, SolverError, SolverView};
use super::types::{Substitution, Type, TypeEnvIdx, TypeIndex, TypeList};
use crate::index::index_newtype;

index_newtype!(AggregateIdx);

/// Size and alignment of a value in linear memory.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct Layout {
	pub(super) size: u32,
	pub(super) align: u32,
}

/// A struct's or a tuple's layout.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) struct AggregateLayout {
	pub(super) layout: Layout,
	/// Each field's byte offset, by declared index.
	pub(super) fields: Box<[u32]>,
	/// The aggregate as Wasm values, nested aggregates flattened, in
	/// declaration order: each value's primitive and its byte offset from the
	/// aggregate's start.
	pub(super) values: Box<[(Primitive, u32)]>,
	/// Field `i` owns `values[field_values[i]..field_values[i + 1]]`; the last
	/// entry is `values.len()`.
	pub(super) field_values: Box<[u32]>,
}

/// What an aggregate's layout is remembered by: its normalized type, read
/// from the interner, so equal types give equal keys.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum AggregateKey {
	Struct(StructIdx, TypeList),
	Tuple(TypeList),
}

/// The layouts the solver has computed.
#[derive(Default)]
pub(super) struct Layouts {
	keys: FxHashMap<AggregateKey, AggregateIdx>,
	aggregates: Vec<AggregateLayout>,
	/// The index of every aggregate layout, found by its contents.
	lookup: HashTable<AggregateIdx>,
	hasher: FxBuildHasher,
}

/// One value as linear memory holds it: an integer of a width and a
/// signedness, or a float. A `bool` is held as a `u8`, a `char` as a `u32`,
/// and an address as its memory's `Size`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Primitive {
	U8,
	I8,
	U16,
	I16,
	U32,
	I32,
	U64,
	I64,
	F32,
	F64,
}

impl Primitive {
	/// The primitive a value of `ty` is held as, if `ty` is one.
	fn of(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::U8 | TypeIndex::BOOL => Self::U8,
			TypeIndex::I8 => Self::I8,
			TypeIndex::U16 => Self::U16,
			TypeIndex::I16 => Self::I16,
			TypeIndex::U32 | TypeIndex::CHAR => Self::U32,
			TypeIndex::I32 => Self::I32,
			TypeIndex::U64 => Self::U64,
			TypeIndex::I64 => Self::I64,
			TypeIndex::F32 => Self::F32,
			TypeIndex::F64 => Self::F64,
			_ => return None,
		})
	}

	/// The bytes it takes, which is also its alignment.
	pub(super) fn size(self) -> u32 {
		match self {
			Self::U8 | Self::I8 => 1,
			Self::U16 | Self::I16 => 2,
			Self::U32 | Self::I32 | Self::F32 => 4,
			Self::U64 | Self::I64 | Self::F64 => 8,
		}
	}
}

/// A laid-out value, as a field contributes to its aggregate.
#[derive(Clone, Copy)]
enum Piece {
	/// No bytes and no values.
	Empty,
	/// `count` values of `primitive`, one after another: one for a primitive
	/// type or an address, two for a slice (its address and its length).
	Primitives {
		primitive: Primitive,
		count: u32,
	},
	Aggregate(AggregateIdx),
}

impl Layouts {
	pub(super) fn aggregate(&self, index: AggregateIdx) -> &AggregateLayout {
		&self.aggregates[usize::from(index)]
	}

	fn layout(&self, piece: Piece) -> Layout {
		match piece {
			Piece::Empty => Layout { size: 0, align: 1 },
			Piece::Primitives { primitive, count } => Layout {
				size: primitive.size() * count,
				align: primitive.size(),
			},
			Piece::Aggregate(index) => self.aggregate(index).layout,
		}
	}

	/// Places `fields` (in declaration order) in `order`.
	fn place(&self, fields: &[Piece], order: FieldOrder) -> AggregateLayout {
		let layouts: Vec<Layout> =
			fields.iter().map(|&field| self.layout(field)).collect();
		let mut placed: Vec<usize> = (0..fields.len()).collect();
		if order == FieldOrder::Optimal {
			placed.sort_by_key(|&at| std::cmp::Reverse(layouts[at].align));
		}
		let (mut size, mut align) = (0u32, 1);
		let mut offsets = vec![0; fields.len()];
		for at in placed {
			size = size.next_multiple_of(layouts[at].align);
			offsets[at] = size;
			size += layouts[at].size;
			align = align.max(layouts[at].align);
		}

		let mut values = Vec::new();
		let mut field_values = Vec::with_capacity(fields.len() + 1);
		for (&field, &base) in fields.iter().zip(&offsets) {
			field_values.push(u32::try_from(values.len()).unwrap());
			match field {
				Piece::Empty => {}
				Piece::Primitives { primitive, count } => values.extend(
					(0..count)
						.map(|at| (primitive, base + at * primitive.size())),
				),
				Piece::Aggregate(index) => values.extend(
					self.aggregate(index)
						.values
						.iter()
						.map(|&(primitive, offset)| (primitive, base + offset)),
				),
			}
		}
		field_values.push(u32::try_from(values.len()).unwrap());

		AggregateLayout {
			layout: Layout {
				size: size.next_multiple_of(align),
				align,
			},
			fields: offsets.into_boxed_slice(),
			values: values.into_boxed_slice(),
			field_values: field_values.into_boxed_slice(),
		}
	}

	/// The index of `layout`, stored only if no equal one is.
	fn intern(&mut self, layout: AggregateLayout) -> AggregateIdx {
		let hash = self.hasher.hash_one(&layout);
		let Self {
			aggregates,
			lookup,
			hasher,
			..
		} = self;
		if let Some(&index) =
			lookup.find(hash, |&index| aggregates[usize::from(index)] == layout)
		{
			return index;
		}
		let index = AggregateIdx::new(u32::try_from(aggregates.len()).unwrap());
		aggregates.push(layout);
		lookup.insert_unique(hash, index, |&index| {
			hasher.hash_one(&aggregates[usize::from(index)])
		});
		index
	}
}

impl Solver {
	/// The layout of a value of `ty` in linear memory. `None` when the
	/// compiler does not know its bytes: some part of it is abstract (a
	/// parameter, a projection that does not reduce, an address into a memory
	/// not known yet), or it is a reference, which Wasm keeps out of linear
	/// memory. A struct containing itself is `Poisoned` (it is reported on
	/// the struct), and one growing without end through its type arguments
	/// overflows.
	pub(super) fn memory_layout(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Layout>, SolverError> {
		let piece =
			self.piece(view, assumption_context, ty, &mut Vec::new())?;
		Ok(piece.map(|piece| self.layouts.layout(piece)))
	}

	/// The layout of a value of `ty`, as `memory_layout` answers it, and
	/// the values it holds: each one's primitive and its byte offset, in
	/// declaration order (an aggregate's `values`).
	pub(super) fn memory_values(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<(Layout, Box<[(Primitive, u32)]>)>, SolverError> {
		let piece =
			self.piece(view, assumption_context, ty, &mut Vec::new())?;
		Ok(piece.map(|piece| {
			let values = match piece {
				Piece::Empty => Box::default(),
				Piece::Primitives { primitive, count } => (0..count)
					.map(|at| (primitive, at * primitive.size()))
					.collect(),
				Piece::Aggregate(index) => {
					self.layouts.aggregate(index).values.clone()
				}
			};
			(self.layouts.layout(piece), values)
		}))
	}

	/// The layout of a struct or a tuple, as `memory_layout` answers it.
	/// `None` for any other type, too.
	pub(super) fn aggregate_layout(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<AggregateIdx>, SolverError> {
		let piece =
			self.piece(view, assumption_context, ty, &mut Vec::new())?;
		Ok(match piece {
			Some(Piece::Aggregate(index)) => Some(index),
			_ => None,
		})
	}

	/// `visiting` holds the aggregates being laid out, normalized: reaching
	/// one again is a struct containing itself.
	fn piece(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		visiting: &mut Vec<TypeIndex>,
	) -> Result<Option<Piece>, SolverError> {
		let ty = self.normalize_head_query(view, assumption_context, ty)?;
		let piece = match *view.types.resolve(ty) {
			Type::Error
			| Type::Infer
			| Type::Integer
			| Type::Float
			| Type::String
			| Type::ArrayLiteral
			| Type::Value { .. }
			| Type::Const { .. } => return Err(SolverError::Poisoned),
			Type::Never
			| Type::Function { .. }
			| Type::Memory { .. }
			| Type::Global { .. } => Piece::Empty,
			Type::U8
			| Type::I8
			| Type::U16
			| Type::I16
			| Type::U32
			| Type::I32
			| Type::U64
			| Type::I64
			| Type::F32
			| Type::F64
			| Type::Bool
			| Type::Char => Piece::Primitives {
				primitive: Primitive::of(ty).expect("a primitive type"),
				count: 1,
			},
			Type::FunctionRef { .. }
			| Type::TypeParam { .. }
			| Type::AssocTypeProjection { .. } => return Ok(None),
			Type::Enum { enum_index } => {
				let repr = view.enums[usize::from(enum_index)].repr;
				return self.piece(view, assumption_context, repr, visiting);
			}
			Type::Pointer { memory, .. } | Type::Array { memory, .. } => {
				let Some(primitive) =
					self.address_primitive(view, assumption_context, memory)?
				else {
					return Ok(None);
				};
				Piece::Primitives {
					primitive,
					count: 1,
				}
			}
			Type::Slice { memory, .. } => {
				let Some(primitive) =
					self.address_primitive(view, assumption_context, memory)?
				else {
					return Ok(None);
				};
				Piece::Primitives {
					primitive,
					count: 2,
				}
			}
			Type::Tuple { .. } | Type::Struct { .. } => {
				return self.aggregate_piece(
					view,
					assumption_context,
					ty,
					visiting,
				);
			}
		};
		Ok(Some(piece))
	}

	fn aggregate_piece(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
		visiting: &mut Vec<TypeIndex>,
	) -> Result<Option<Piece>, SolverError> {
		let ty = self.normalize_type_query(view, assumption_context, ty)?;
		let key = match *view.types.resolve(ty) {
			Type::Struct {
				struct_index,
				type_args,
			} => AggregateKey::Struct(struct_index, type_args),
			Type::Tuple { elements } => AggregateKey::Tuple(elements),
			_ => unreachable!("normalizing deeper keeps a struct or a tuple"),
		};
		let concrete =
			!view.types.has_param(ty) && !view.types.has_projection(ty);
		if concrete && let Some(&index) = self.layouts.keys.get(&key) {
			return Ok(Some(Piece::Aggregate(index)));
		}
		if visiting.contains(&ty) {
			return Err(SolverError::Poisoned);
		}
		if visiting.len() > self.state.recursion_budget {
			return Err(SolverError::Overflow);
		}
		let (order, fields) = match key {
			AggregateKey::Struct(struct_index, type_args) => {
				let signature = &view.structs[usize::from(struct_index)];
				let (env, field_types) =
					(signature.type_params, signature.field_types);
				let args: Box<[TypeIndex]> = view.types.list(type_args).into();
				// Read one field at a time: substituting may store more lists.
				let mut fields = Vec::with_capacity(field_types.len());
				for at in 0..field_types.len() {
					let field = view.types.list(field_types)[at];
					fields.push(view.types.substitute(
						field,
						Substitution {
							envs: view.type_envs,
							env,
							args: &args,
						},
					));
				}
				(view.defs.structs[usize::from(struct_index)].order, fields)
			}
			AggregateKey::Tuple(elements) => {
				(FieldOrder::Optimal, view.types.list(elements).to_vec())
			}
		};

		visiting.push(ty);
		let mut pieces = Vec::with_capacity(fields.len());
		for field in fields {
			match self.piece(view, assumption_context, field, visiting) {
				Ok(Some(piece)) => pieces.push(piece),
				unknown => {
					visiting.pop();
					return unknown;
				}
			}
		}
		visiting.pop();

		let layout = self.layouts.place(&pieces, order);
		let index = self.layouts.intern(layout);
		if concrete {
			self.layouts.keys.insert(key, index);
		}
		Ok(Some(Piece::Aggregate(index)))
	}

	/// The primitive of an address into `memory`, its `Size`. `None` for a
	/// memory not known yet.
	fn address_primitive(
		&mut self,
		view: &mut SolverView<'_>,
		assumption_context: TypeEnvIdx,
		memory: TypeIndex,
	) -> Result<Option<Primitive>, SolverError> {
		let memory =
			self.normalize_head_query(view, assumption_context, memory)?;
		let Type::Memory { memory_index } = *view.types.resolve(memory) else {
			return Ok(None);
		};
		let size =
			view.defs.memories[usize::from(memory_index)].size_assoc_type_index;
		let Some(size) = view.assoc_types[usize::from(size)]
			.as_ref()
			.and_then(|signature| signature.value)
		else {
			return Err(SolverError::Pending);
		};
		let size = self.normalize_head_query(view, assumption_context, size)?;
		Primitive::of(size).map(Some).ok_or(SolverError::Poisoned)
	}
}

impl TypeContext<'_, '_, '_> {
	pub(super) fn memory_values(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<(Layout, Box<[(Primitive, u32)]>)>, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.memory_values(&mut view, assumption_context, ty)
	}

	#[allow(dead_code)] // Constant evaluation is its first caller.
	pub(super) fn memory_layout(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Layout>, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.memory_layout(&mut view, assumption_context, ty)
	}

	#[allow(dead_code)] // Constant evaluation is its first caller.
	pub(super) fn aggregate_layout(
		&mut self,
		assumption_context: TypeEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<AggregateIdx>, SolverError> {
		let (solver, mut view) = self.solver_and_view();
		solver.aggregate_layout(&mut view, assumption_context, ty)
	}

	#[allow(dead_code)] // Constant evaluation is its first caller.
	pub(super) fn aggregate(&self, index: AggregateIdx) -> &AggregateLayout {
		self.solver.layouts.aggregate(index)
	}
}

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;
	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{DiagnosticCode, TextSpan};
	use crate::testing::DiagnosticView;
	use crate::tir::defs::{
		AstEntry, DefKind, DefinitionRegistry, FunctionIdx, Scope, Tier,
	};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::signatures::FunctionSignature;
	use crate::vfs::{self, FileId, Files};

	/// `test_case!(mut case = "source")` declares the graph, the inputs and
	/// the swept `TestCase` borrowing them as three locals of the calling
	/// test. The source plays the stdlib's role, so it declares the
	/// primitives and traits it uses.
	macro_rules! test_case {
		(mut $case:ident = $source:expr $(,)?) => {
			let mut graph = source_graph($source);
			let mut inputs = TestInputs::new(&mut graph);
			let mut $case = TestCase::new(&mut inputs);
		};
	}

	fn source_graph(source: &str) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		builder.set_stdlib(root_id);
		builder.build(root_id)
	}

	/// Everything a `TypeContext` borrows, kept on the test's stack.
	struct TestInputs<'g> {
		files: &'g Files,
		strings: &'g mut StringInterner,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let vfs::CompilationUnit {
				files,
				packages,
				strings,
				stdlib_package,
				root_package,
			} = graph;
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				packages,
				files,
				strings,
				&mut diagnostics,
				&mut resolutions,
				*stdlib_package,
				*root_package,
			);
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				strings,
				&defs,
				&ast_nodes,
			);
			Self {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			}
		}
	}

	/// A swept `TypeContext` over `TestInputs`.
	struct TestCase<'a> {
		defs: &'a DefinitionRegistry,
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				strings,
				files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			Self { defs, context }
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"layout",
				&self.context.diagnostics,
				self.context.files,
			)
		}

		/// The function a root-level `name` resolves to, by real path
		/// resolution.
		fn function(&self, name: &str) -> FunctionIdx {
			let root = Scope::Package(self.defs.root_package);
			let file_id = self.defs.namespaces.file_id(root.into());
			let segment = ast::PathSegment {
				ident: Spanned {
					inner: self
						.context
						.strings
						.get(name)
						.expect("already interned from source"),
					span: TextSpan::new(0, 0),
				},
				type_args: Box::new([]),
			};
			let mut scratch = Vec::new();
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut scratch,
				&mut resolutions,
				self.context.strings,
				self.defs,
			)
			.resolve_path(file_id, root, &[segment], Tier::Value);
			let def_key = target.def_key().unwrap_or_else(|| {
				panic!("expected `{name}` to resolve: {scratch:?}")
			});
			let DefKind::Function(index) = def_key.symbol_kind(self.defs)
			else {
				panic!("expected `{name}` to be a function");
			};
			index
		}

		fn function_signature(&self, name: &str) -> &FunctionSignature {
			&self.context.functions[usize::from(self.function(name))]
		}

		fn param_types(&self, name: &str) -> &[TypeIndex] {
			self.context
				.types
				.list(self.function_signature(name).param_types)
		}
	}
	/// The declarations a layout test builds on: a 32-bit and a 64-bit
	/// memory.
	fn with_memories(source: &str) -> String {
		format!(
			"{}\n{source}",
			indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8; type u16; type u32; type u64; type f64; type bool; type char;
			typeset PointerSize { u32, u64 }
			trait Memory { type Size: PointerSize; }
			memory heap: u32;
			memory wide: u64;
		"}
		)
	}

	/// The layout of parameter `index` of function `path`, in the
	/// function's own scope.
	fn param_layout(
		case: &mut TestCase<'_>,
		path: &str,
		index: usize,
	) -> Result<Option<Layout>, SolverError> {
		let scope = case.function_signature(path).type_params;
		let ty = case.param_types(path)[index];
		case.context.memory_layout(scope, ty)
	}

	/// The aggregate layout of parameter `index` of function `path`.
	fn param_aggregate(
		case: &mut TestCase<'_>,
		path: &str,
		index: usize,
	) -> Option<AggregateIdx> {
		let scope = case.function_signature(path).type_params;
		let ty = case.param_types(path)[index];
		case.context
			.aggregate_layout(scope, ty)
			.expect("a parameter's layout is final")
	}

	fn param_aggregate_layout(
		case: &mut TestCase<'_>,
		path: &str,
		index: usize,
	) -> AggregateLayout {
		let aggregate = param_aggregate(case, path, index)
			.expect("the parameter is a struct or a tuple");
		case.context.aggregate(aggregate).clone()
	}

	fn known(size: u32, align: u32) -> Option<Layout> {
		Some(Layout { size, align })
	}

	fn aggregate(
		(size, align): (u32, u32),
		fields: &[u32],
		values: &[(Primitive, u32)],
		field_values: &[u32],
	) -> AggregateLayout {
		AggregateLayout {
			layout: Layout { size, align },
			fields: fields.into(),
			values: values.into(),
			field_values: field_values.into(),
		}
	}

	#[test]
	fn primitives_and_addresses_take_their_width() {
		let source = with_memories(indoc! {"
			enum Small(u16) { A = 0 }
			func f(
				a: u8, b: u16, c: u32, d: u64, e: bool, g: f64,
				h: heap::&u8, i: wide::*u64, j: heap::&[u8; 4],
				k: heap::&[u8], l: wide::&[u8], m: (), n: Small,
			) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		let expected = [
			known(1, 1),
			known(2, 2),
			known(4, 4),
			known(8, 8),
			known(1, 1),
			known(8, 8),
			known(4, 4),
			known(8, 8),
			known(4, 4),
			known(8, 4),
			known(16, 8),
			known(0, 1),
			known(2, 2),
		];
		for (index, expected) in expected.into_iter().enumerate() {
			assert_eq!(
				param_layout(&mut case, "f", index),
				Ok(expected),
				"parameter {index}"
			);
		}
		// Only a struct or a tuple has an aggregate layout.
		assert_eq!(param_aggregate(&mut case, "f", 9), None);
	}

	#[test]
	fn fields_are_sorted_by_alignment_unless_fixed() {
		let source = with_memories(indoc! {"
			struct Mixed(a: u8, b: u64, c: u16, d: u8);
			#[fixed_order]
			struct Fixed(a: u8, b: u64, c: u16, d: u8);
			struct Empty();
			func f(a: Mixed, b: Fixed, c: (u8, u64, u16), d: Empty) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		// `b` at 0, `c` at 8, then `a` and `d` in declaration order. The
		// values stay in declaration order, whatever their offsets.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 0),
			aggregate(
				(16, 8),
				&[10, 0, 8, 11],
				&[
					(Primitive::U8, 10),
					(Primitive::U64, 0),
					(Primitive::U16, 8),
					(Primitive::U8, 11)
				],
				&[0, 1, 2, 3, 4],
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 1),
			aggregate(
				(24, 8),
				&[0, 8, 16, 18],
				&[
					(Primitive::U8, 0),
					(Primitive::U64, 8),
					(Primitive::U16, 16),
					(Primitive::U8, 18)
				],
				&[0, 1, 2, 3, 4],
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 2),
			aggregate(
				(16, 8),
				&[10, 0, 8],
				&[
					(Primitive::U8, 10),
					(Primitive::U64, 0),
					(Primitive::U16, 8)
				],
				&[0, 1, 2, 3],
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 3),
			aggregate((0, 1), &[], &[], &[0])
		);
	}

	#[test]
	fn a_nested_aggregate_is_flattened_at_its_offset() {
		let source = with_memories(indoc! {"
			enum Small(u16) { A = 0 }
			struct Text(len: u8, bytes: heap::&[u8]);
			struct Outer(a: u8, inner: Text);
			struct WideText(len: u8, bytes: wide::&[u8]);
			struct Tagged(tag: Small, x: u32);
			struct Pair<T>(T, T);
			func f(
				a: Text, b: Outer, c: WideText, d: Tagged,
				e: Pair<Pair<u8>>,
			) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		// A slice is two values: its address, then its length.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 0),
			aggregate(
				(12, 4),
				&[8, 0],
				&[(Primitive::U8, 8), (Primitive::U32, 0), (Primitive::U32, 4)],
				&[0, 1, 3],
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 1),
			aggregate(
				(16, 4),
				&[12, 0],
				&[
					(Primitive::U8, 12),
					(Primitive::U8, 8),
					(Primitive::U32, 0),
					(Primitive::U32, 4)
				],
				&[0, 1, 4],
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 2),
			aggregate(
				(24, 8),
				&[16, 0],
				&[
					(Primitive::U8, 16),
					(Primitive::U64, 0),
					(Primitive::U64, 8)
				],
				&[0, 1, 3],
			)
		);
		// An enum is its repr.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 3),
			aggregate(
				(8, 4),
				&[4, 0],
				&[(Primitive::U16, 4), (Primitive::U32, 0)],
				&[0, 1, 2],
			)
		);
		// A struct nested in itself with other arguments is no loop.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 4),
			aggregate(
				(4, 1),
				&[0, 2],
				&[
					(Primitive::U8, 0),
					(Primitive::U8, 1),
					(Primitive::U8, 2),
					(Primitive::U8, 3)
				],
				&[0, 2, 4],
			)
		);
	}

	#[test]
	fn a_bool_is_held_as_a_u8_and_a_char_as_a_u32() {
		let source = with_memories(indoc! {"
			struct Letter(upper: bool, code: char);
			func f(a: Letter) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 0),
			aggregate(
				(8, 4),
				&[4, 0],
				&[(Primitive::U8, 4), (Primitive::U32, 0)],
				&[0, 1, 2],
			)
		);
	}

	#[test]
	fn types_of_one_layout_share_it() {
		let source = with_memories(indoc! {"
			struct Pair<A, B>(A, B);
			struct Named(x: u32, y: u8);
			#[fixed_order]
			struct Swapped(u8, u32);
			struct Wrap<T>(T);
			func f<T>(
				a: Pair<u32, u8>, b: (u32, u8), c: Named, d: Swapped,
				e: Wrap<heap::&T>, g: Wrap<heap::&u8>,
			) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		let pair = param_aggregate(&mut case, "f", 0);
		assert!(pair.is_some());
		assert_eq!(param_aggregate(&mut case, "f", 0), pair);
		assert_eq!(param_aggregate(&mut case, "f", 1), pair);
		assert_eq!(param_aggregate(&mut case, "f", 2), pair);
		// Same size and offsets, but its values are in another order.
		assert_ne!(param_aggregate(&mut case, "f", 3), pair);
		// A layout that does not depend on `T` is known, and shared.
		let wrap = param_aggregate(&mut case, "f", 5);
		assert!(wrap.is_some());
		assert_eq!(param_aggregate(&mut case, "f", 4), wrap);
	}

	#[test]
	fn an_abstract_part_or_a_reference_has_no_layout() {
		let source = with_memories(indoc! {"
			struct Wrap<T>(T);
			func f<T, Mem: Memory>(
				a: T, b: Wrap<T>, c: heap::&T, d: Mem::&u8,
				e: func(u32) -> u32, g: (u8, func(u32) -> u32),
			) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics().assert_none();
		assert_eq!(param_layout(&mut case, "f", 0), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 1), Ok(None));
		// An address is as wide as its memory, whatever it points to.
		assert_eq!(param_layout(&mut case, "f", 2), Ok(known(4, 4)));
		assert_eq!(param_layout(&mut case, "f", 3), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 4), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 5), Ok(None));
	}

	#[test]
	fn a_struct_containing_itself_has_no_layout() {
		let source = with_memories(indoc! {"
			struct Selfish(s: Selfish);
			func f(x: Selfish) {}
		"});
		test_case!(mut case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RecursiveTypeWithoutIndirection]);
		assert_eq!(param_layout(&mut case, "f", 0), Err(SolverError::Poisoned));
	}
}
