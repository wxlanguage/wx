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
//! layout. Anything else is a direct mapping and is never stored. A layout's
//! fields and scalars are rows of two columns shared by every layout
//! (`Layouts::field_offsets`, `Layouts::scalars`), and it holds a run of
//! each.
//!
//! This is memory only. How a value is held on the Wasm stack (its scalars'
//! types, and which of them each field is) is lowering's
//! (`tir/lower/shapes.rs`), its only reader.

use std::hash::BuildHasher;

use hashbrown::HashTable;
use rustc_hash::{FxBuildHasher, FxHashMap};

use super::bounds::AssumptionEnvIdx;
use super::decls::{FieldOrder, StructIdx};
use super::signatures::Semantics;
use super::solver::{
	NormalizationDepth, RewriteFlags, SolverError, metadata_len,
};
use super::types::{Primitive, Substitution, Type, TypeIndex, TypeList};
use crate::ast::StringInterner;
use crate::index::index_newtype;

index_newtype!(AggregateIdx);

/// Size and alignment of a value in linear memory.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct Layout {
	pub(super) size: u32,
	pub(super) align: u32,
}

/// A struct's or a tuple's layout: its size and alignment, and its rows in
/// `Layouts`' columns.
#[derive(Clone, Copy)]
struct AggregateLayout {
	layout: Layout,
	fields: FieldList,
	scalars: ScalarList,
}

/// A run of `Layouts::field_offsets`: one row per field, by declared index.
#[derive(Clone, Copy)]
struct FieldList {
	start: u32,
	len: u32,
}

/// A run of `Layouts::scalars`: one row per Wasm value, in declaration
/// pre-order.
#[derive(Clone, Copy)]
struct ScalarList {
	start: u32,
	len: u32,
}

fn rows<T>(column: &[T], start: u32, len: u32) -> &[T] {
	&column[start as usize..(start + len) as usize]
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
	/// Each field's byte offset from its aggregate's start.
	field_offsets: Vec<u32>,
	/// Each Wasm value an aggregate holds, nested aggregates flattened, in
	/// declaration order: its primitive and its byte offset from the
	/// aggregate's start. An array field holds none: an aggregate holding
	/// one is no `StackValue`, so it is never one value.
	scalars: Vec<(Primitive, u32)>,
	/// The index of every aggregate layout, found by its contents.
	lookup: HashTable<AggregateIdx>,
	hasher: FxBuildHasher,
}

/// A laid-out value, as a field contributes to its aggregate, and as a
/// load or a store reads where its scalars are (`Layouts::scalar`).
#[derive(Clone, Copy)]
pub(super) enum Piece {
	/// No bytes and no values.
	Empty,
	/// `count` values of `primitive`, one after another: one for a primitive
	/// type or an address, two for a slice (its address and its length).
	Primitives {
		primitive: Primitive,
		count: u32,
	},
	Aggregate(AggregateIdx),
	/// An array of a known length: its elements' bytes, one after another,
	/// and no values (`memory_values` repeats its element's).
	Array(Layout),
}

impl Layouts {
	/// Each field's byte offset, by declared index.
	pub(super) fn field_offsets(&self, index: AggregateIdx) -> &[u32] {
		let fields = self.aggregates[usize::from(index)].fields;
		rows(&self.field_offsets, fields.start, fields.len)
	}

	/// Each Wasm value's primitive and byte offset, in declaration order.
	pub(super) fn scalars(&self, index: AggregateIdx) -> &[(Primitive, u32)] {
		let scalars = self.aggregates[usize::from(index)].scalars;
		rows(&self.scalars, scalars.start, scalars.len)
	}

	/// How many Wasm values `piece` holds.
	pub(super) fn scalar_count(&self, piece: Piece) -> usize {
		match piece {
			Piece::Empty | Piece::Array(_) => 0,
			Piece::Primitives { count, .. } => count as usize,
			Piece::Aggregate(index) => {
				self.aggregates[usize::from(index)].scalars.len as usize
			}
		}
	}

	/// `piece`'s Wasm value `at`: the primitive it is in memory and its
	/// byte offset from the start.
	pub(super) fn scalar(&self, piece: Piece, at: usize) -> (Primitive, u32) {
		match piece {
			Piece::Primitives { primitive, count } => {
				assert!(at < count as usize, "a scalar of the value");
				(primitive, at as u32 * primitive.size())
			}
			Piece::Aggregate(index) => self.scalars(index)[at],
			Piece::Empty | Piece::Array(_) => {
				unreachable!("an empty value or an array holds no scalar")
			}
		}
	}

	pub(super) fn layout(&self, piece: Piece) -> Layout {
		match piece {
			Piece::Empty => Layout { size: 0, align: 1 },
			Piece::Primitives { primitive, count } => Layout {
				size: primitive.size() * count,
				align: primitive.size(),
			},
			Piece::Aggregate(index) => {
				self.aggregates[usize::from(index)].layout
			}
			Piece::Array(layout) => layout,
		}
	}

	/// Places `fields` (in declaration order) in `order` and stores the
	/// layout, once per distinct content.
	fn place(&mut self, fields: &[Piece], order: FieldOrder) -> AggregateIdx {
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

		let mut scalars = Vec::new();
		for (&field, &base) in fields.iter().zip(&offsets) {
			match field {
				Piece::Empty | Piece::Array(_) => {}
				Piece::Primitives { primitive, count } => scalars.extend(
					(0..count)
						.map(|at| (primitive, base + at * primitive.size())),
				),
				Piece::Aggregate(index) => scalars.extend(
					self.scalars(index)
						.iter()
						.map(|&(primitive, offset)| (primitive, base + offset)),
				),
			}
		}

		let layout = Layout {
			size: size.next_multiple_of(align),
			align,
		};
		self.intern(layout, &offsets, &scalars)
	}

	/// The index of the layout with these rows, stored only if no equal one
	/// is: its rows are appended to the columns then.
	fn intern(
		&mut self,
		layout: Layout,
		field_offsets: &[u32],
		scalars: &[(Primitive, u32)],
	) -> AggregateIdx {
		let hash = self.hasher.hash_one((layout, field_offsets, scalars));
		let Self {
			aggregates,
			field_offsets: offset_column,
			scalars: scalar_column,
			lookup,
			hasher,
			..
		} = self;
		if let Some(&index) = lookup.find(hash, |&index| {
			let aggregate = &aggregates[usize::from(index)];
			contents(aggregate, offset_column, scalar_column)
				== (layout, field_offsets, scalars)
		}) {
			return index;
		}
		let index = AggregateIdx::new(u32::try_from(aggregates.len()).unwrap());
		aggregates.push(AggregateLayout {
			layout,
			fields: FieldList {
				start: u32::try_from(offset_column.len()).unwrap(),
				len: u32::try_from(field_offsets.len()).unwrap(),
			},
			scalars: ScalarList {
				start: u32::try_from(scalar_column.len()).unwrap(),
				len: u32::try_from(scalars.len()).unwrap(),
			},
		});
		offset_column.extend_from_slice(field_offsets);
		scalar_column.extend_from_slice(scalars);
		lookup.insert_unique(hash, index, |&index| {
			let aggregate = &aggregates[usize::from(index)];
			hasher.hash_one(contents(aggregate, offset_column, scalar_column))
		});
		index
	}
}

/// What an aggregate layout is compared and hashed by: its size and
/// alignment, and its rows.
fn contents<'a>(
	aggregate: &AggregateLayout,
	field_offsets: &'a [u32],
	scalars: &'a [(Primitive, u32)],
) -> (Layout, &'a [u32], &'a [(Primitive, u32)]) {
	(
		aggregate.layout,
		rows(field_offsets, aggregate.fields.start, aggregate.fields.len),
		rows(scalars, aggregate.scalars.start, aggregate.scalars.len),
	)
}

impl Semantics {
	/// The layout of a value of `ty` in linear memory. `None` when the
	/// compiler does not know its bytes: some part of it is abstract (a
	/// parameter, a projection that does not reduce, an address into a memory
	/// not known yet), or it is a reference, which Wasm keeps out of linear
	/// memory. A struct containing itself is `Poisoned` (it is reported on
	/// the struct), and one growing without end through its type arguments
	/// overflows.
	pub(super) fn memory_layout(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Layout>, SolverError> {
		let piece =
			self.piece(strings, assumption_context, ty, &mut Vec::new())?;
		Ok(piece.map(|piece| self.solver.layouts.layout(piece)))
	}

	/// The layout of a value of `ty`, as `memory_layout` answers it, and
	/// the values it holds: each one's primitive and its byte offset, in
	/// declaration order (an aggregate's `values`; an array's element's,
	/// once per element, as static data writes it).
	pub(super) fn memory_values(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<(Layout, Box<[(Primitive, u32)]>)>, SolverError> {
		let Some(piece) =
			self.piece(strings, assumption_context, ty, &mut Vec::new())?
		else {
			return Ok(None);
		};
		let values = match piece {
			Piece::Empty => Box::default(),
			Piece::Primitives { primitive, count } => (0..count)
				.map(|at| (primitive, at * primitive.size()))
				.collect(),
			Piece::Aggregate(index) => {
				self.solver.layouts.scalars(index).into()
			}
			Piece::Array(_) => {
				let ty = self.normalize(
					strings,
					assumption_context,
					ty,
					NormalizationDepth::Shallow,
					RewriteFlags::ALL,
				)?;
				let Type::Array { of, .. } = *self.types.resolve(ty) else {
					unreachable!("an array's piece is an array's")
				};
				let Some((element, values)) =
					self.memory_values(strings, assumption_context, of)?
				else {
					unreachable!(
						"an array with a layout has an element with one"
					)
				};
				let count = match element.size {
					0 => 0,
					size => self.solver.layouts.layout(piece).size / size,
				};
				(0..count)
					.flat_map(|at| {
						values.iter().map(move |&(primitive, offset)| {
							(primitive, at * element.size + offset)
						})
					})
					.collect()
			}
		};
		Ok(Some((self.solver.layouts.layout(piece), values)))
	}

	/// Where a value of `ty`'s bytes and scalars are, as `memory_layout`
	/// answers its layout; read a scalar's offset with
	/// `Layouts::scalar`, with no copy of the aggregate's rows.
	pub(super) fn memory_piece(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<Piece>, SolverError> {
		self.piece(strings, assumption_context, ty, &mut Vec::new())
	}

	/// The layout of a struct or a tuple, as `memory_layout` answers it.
	/// `None` for any other type, too.
	pub(super) fn aggregate_layout(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Result<Option<AggregateIdx>, SolverError> {
		let piece =
			self.piece(strings, assumption_context, ty, &mut Vec::new())?;
		Ok(match piece {
			Some(Piece::Aggregate(index)) => Some(index),
			_ => None,
		})
	}

	/// `visiting` holds the aggregates being laid out, normalized: reaching
	/// one again is a struct containing itself.
	fn piece(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
		visiting: &mut Vec<TypeIndex>,
	) -> Result<Option<Piece>, SolverError> {
		let ty = self.normalize(
			strings,
			assumption_context,
			ty,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		)?;
		let piece = match *self.types.resolve(ty) {
			Type::Error
			| Type::Infer
			| Type::ConstInt
			| Type::ConstFloat
			| Type::ConstChar
			| Type::Value { .. }
			| Type::ConstRef { .. } => return Err(SolverError::Poisoned),
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
			| Type::F64 => Piece::Primitives {
				primitive: Primitive::of(ty).expect("a primitive type"),
				count: 1,
			},
			Type::Funcref
			| Type::TypedFuncref { .. }
			| Type::TypeParam { .. }
			| Type::TypeProjection { .. } => return Ok(None),
			Type::Enum { enum_index } => {
				let repr = self.enums[usize::from(enum_index)].repr;
				return self.piece(strings, assumption_context, repr, visiting);
			}
			// An address, then the pointee's counts, each as wide as the
			// memory's `Size`.
			Type::Pointer { to, memory, .. } => {
				let Some(primitive) = self.address_primitive(
					strings,
					assumption_context,
					memory,
				)?
				else {
					return Ok(None);
				};
				let Some(metadata) = self.pointer_metadata(
					strings,
					assumption_context,
					to,
					memory,
				)?
				else {
					return Ok(None);
				};
				Piece::Primitives {
					primitive,
					count: 1 + metadata_len(&self.types, metadata) as u32,
				}
			}
			// An array of a known length is its elements, one after another.
			// A slice has no size, nor does an array of an abstract length.
			Type::Array { of, length } => {
				let length = self.normalize(
					strings,
					assumption_context,
					length,
					NormalizationDepth::Shallow,
					RewriteFlags::ALL,
				)?;
				let Type::Value { bits } = *self.types.resolve(length) else {
					return Ok(None);
				};
				let Some(element) =
					self.piece(strings, assumption_context, of, visiting)?
				else {
					return Ok(None);
				};
				let element = self.solver.layouts.layout(element);
				let size = u32::try_from(bits)
					.ok()
					.and_then(|count| element.size.checked_mul(count))
					.ok_or(SolverError::Overflow)?;
				Piece::Array(Layout {
					size,
					align: element.align,
				})
			}
			Type::Slice { .. } => return Ok(None),
			Type::Tuple { .. } | Type::Struct { .. } => {
				return self.aggregate_piece(
					strings,
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
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		ty: TypeIndex,
		visiting: &mut Vec<TypeIndex>,
	) -> Result<Option<Piece>, SolverError> {
		let ty = self.normalize(
			strings,
			assumption_context,
			ty,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		let key = match *self.types.resolve(ty) {
			Type::Struct {
				struct_index,
				type_args,
			} => AggregateKey::Struct(struct_index, type_args),
			Type::Tuple { elements } => AggregateKey::Tuple(elements),
			_ => unreachable!("normalizing deeper keeps a struct or a tuple"),
		};
		let concrete =
			!self.types.has_param(ty) && !self.types.has_projection(ty);
		if concrete && let Some(&index) = self.solver.layouts.keys.get(&key) {
			return Ok(Some(Piece::Aggregate(index)));
		}
		if visiting.contains(&ty) {
			return Err(SolverError::Poisoned);
		}
		if visiting.len() > self.solver.state.recursion_budget {
			return Err(SolverError::Overflow);
		}
		let (order, fields) = match key {
			AggregateKey::Struct(struct_index, type_args) => {
				let signature = &self.structs[usize::from(struct_index)];
				let (env, field_types) =
					(signature.type_params, signature.field_types);
				let args: Box<[TypeIndex]> = self.types.list(type_args).into();
				// Read one field at a time: substituting may store more lists.
				let mut fields = Vec::with_capacity(field_types.len());
				for at in 0..field_types.len() {
					let field = self.types.list(field_types)[at];
					fields.push(self.types.substitute(
						field,
						Substitution {
							envs: &self.generic_envs,
							env,
							args: &args,
						},
					));
				}
				(self.decls.structs[usize::from(struct_index)].order, fields)
			}
			AggregateKey::Tuple(elements) => {
				(FieldOrder::Optimal, self.types.list(elements).to_vec())
			}
		};

		visiting.push(ty);
		let mut pieces = Vec::with_capacity(fields.len());
		for field in fields {
			match self.piece(strings, assumption_context, field, visiting) {
				Ok(Some(piece)) => pieces.push(piece),
				unknown => {
					visiting.pop();
					return unknown;
				}
			}
		}
		visiting.pop();

		let index = self.solver.layouts.place(&pieces, order);
		if concrete {
			self.solver.layouts.keys.insert(key, index);
		}
		Ok(Some(Piece::Aggregate(index)))
	}

	/// The primitive of an address into `memory`, its `Size`. `None` for a
	/// memory not known yet.
	pub(super) fn address_primitive(
		&mut self,
		strings: &StringInterner,
		assumption_context: AssumptionEnvIdx,
		memory: TypeIndex,
	) -> Result<Option<Primitive>, SolverError> {
		let memory = self.normalize(
			strings,
			assumption_context,
			memory,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		)?;
		let Type::Memory { memory_index } = *self.types.resolve(memory) else {
			return Ok(None);
		};
		let size = self.decls.memories[usize::from(memory_index)]
			.size_assoc_type_index;
		let Some(size) = self.assoc_types[usize::from(size)]
			.as_ref()
			.and_then(|signature| signature.value)
		else {
			return Err(SolverError::Pending);
		};
		let size = self.normalize(
			strings,
			assumption_context,
			size,
			NormalizationDepth::Shallow,
			RewriteFlags::ALL,
		)?;
		Primitive::of(size).map(Some).ok_or(SolverError::Poisoned)
	}
}

#[cfg(test)]
mod tests {
	use indoc::indoc;

	use super::*;
	use crate::ast::{self, Spanned, StringInterner};
	use crate::diagnostics::{DiagnosticCode, TextSpan};
	use crate::testing::DiagnosticView;
	use crate::tir::decls::{DeclKind, FunctionIdx, Scope, Tier};
	use crate::tir::paths::PathResolver;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::signatures::FunctionSignature;
	use crate::tir::signatures::tests::source_graph;
	use crate::vfs::Files;

	/// A checked `Semantics`, with the inputs it was checked from.
	struct TestCase {
		files: Files,
		strings: StringInterner,
		sema: Semantics,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = ast::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let sema = crate::tir::check(&graph, &mut strings);
			Self {
				files: graph.files,
				strings,
				sema,
			}
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new("layout", &self.sema.diagnostics, &self.files)
		}

		/// The function a root-level `name` resolves to, by real path
		/// resolution.
		fn function(&self, name: &str) -> FunctionIdx {
			let root = Scope::Package(self.sema.decls.root_package);
			let file_id = self.sema.decls.namespaces.file_id(root.into());
			let segment = ast::PathSegment::new(Spanned {
				inner: self
					.strings
					.get(name)
					.expect("already interned from source"),
				span: TextSpan::new(0, 0),
			});
			let mut scratch = Vec::new();
			let mut resolutions = NameResolutions::default();
			let target = PathResolver::new(
				&mut scratch,
				&mut resolutions,
				&self.strings,
				&self.sema.decls,
				&[],
			)
			.resolve_path(file_id, root, &[segment], Tier::Value);
			let loc = target.loc().unwrap_or_else(|| {
				panic!("expected `{name}` to resolve: {scratch:?}")
			});
			let DeclKind::Function(index) = loc.symbol_kind(&self.sema.decls)
			else {
				panic!("expected `{name}` to be a function");
			};
			index
		}

		fn function_signature(&self, name: &str) -> &FunctionSignature {
			&self.sema.functions[usize::from(self.function(name))]
		}

		fn param_types(&self, name: &str) -> &[TypeIndex] {
			self.sema
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
			memory heap: u32;
			memory wide: u64;
		"}
		)
	}

	/// The layout of parameter `index` of function `path`, in the
	/// function's own scope.
	fn param_layout(
		case: &mut TestCase,
		path: &str,
		index: usize,
	) -> Result<Option<Layout>, SolverError> {
		let scope = case.function_signature(path).type_params;
		let ty = case.param_types(path)[index];
		case.sema.memory_layout(
			&case.strings,
			case.sema.assumption_envs.of_frame(scope),
			ty,
		)
	}

	/// The aggregate layout of parameter `index` of function `path`.
	fn param_aggregate(
		case: &mut TestCase,
		path: &str,
		index: usize,
	) -> Option<AggregateIdx> {
		let scope = case.function_signature(path).type_params;
		let ty = case.param_types(path)[index];
		case.sema
			.aggregate_layout(
				&case.strings,
				case.sema.assumption_envs.of_frame(scope),
				ty,
			)
			.expect("a parameter's layout is final")
	}

	/// An aggregate layout's contents, read out of the columns.
	#[derive(Debug, PartialEq)]
	struct Contents {
		layout: Layout,
		field_offsets: Vec<u32>,
		scalars: Vec<(Primitive, u32)>,
	}

	fn contents(case: &TestCase, index: AggregateIdx) -> Contents {
		let layouts = &case.sema.solver.layouts;
		Contents {
			layout: layouts.layout(Piece::Aggregate(index)),
			field_offsets: layouts.field_offsets(index).to_vec(),
			scalars: layouts.scalars(index).to_vec(),
		}
	}

	fn param_aggregate_layout(
		case: &mut TestCase,
		path: &str,
		index: usize,
	) -> Contents {
		let aggregate = param_aggregate(case, path, index)
			.expect("the parameter is a struct or a tuple");
		contents(case, aggregate)
	}

	fn known(size: u32, align: u32) -> Option<Layout> {
		Some(Layout { size, align })
	}

	fn aggregate(
		(size, align): (u32, u32),
		field_offsets: &[u32],
		scalars: &[(Primitive, u32)],
	) -> Contents {
		Contents {
			layout: Layout { size, align },
			field_offsets: field_offsets.into(),
			scalars: scalars.into(),
		}
	}

	#[test]
	fn primitives_and_addresses_take_their_width() {
		let source = with_memories(indoc! {"
			enum Small(u16) { A = 0 }
			func f(
				a: u8, b: u16, c: u32, d: u64, e: Bool, g: f64,
				h: heap::&u8, i: wide::*u64, j: heap::&[u8; 4],
				k: heap::&[u8], l: wide::&[u8], m: (), n: Small,
			) {}
		"});
		let mut case = TestCase::new(&source);
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
		let mut case = TestCase::new(&source);
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
			)
		);
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 3),
			aggregate((0, 1), &[], &[])
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
		let mut case = TestCase::new(&source);
		case.diagnostics().assert_none();
		// A slice is two values: its address, then its length.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 0),
			aggregate(
				(12, 4),
				&[8, 0],
				&[(Primitive::U8, 8), (Primitive::U32, 0), (Primitive::U32, 4)],
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
			)
		);
		// An enum is its repr.
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 3),
			aggregate(
				(8, 4),
				&[4, 0],
				&[(Primitive::U16, 4), (Primitive::U32, 0)],
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
			)
		);
	}

	#[test]
	fn a_bool_is_held_as_a_u8_and_a_char_as_a_u32() {
		let source = with_memories(indoc! {"
			struct Letter(upper: Bool, code: Char);
			func f(a: Letter) {}
		"});
		let mut case = TestCase::new(&source);
		case.diagnostics().assert_none();
		assert_eq!(
			param_aggregate_layout(&mut case, "f", 0),
			aggregate(
				(8, 4),
				&[4, 0],
				&[(Primitive::U8, 4), (Primitive::U32, 0)],
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
			func f<T: StackValue>(
				a: Pair<u32, u8>, b: (u32, u8), c: Named, d: Swapped,
				e: Wrap<heap::&T>, g: Wrap<heap::&u8>,
			) {}
		"});
		let mut case = TestCase::new(&source);
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
	fn a_pointer_holds_one_count_per_slice_level() {
		let source = with_memories(indoc! {"
			func f<S: Slice, A: Array>(
				a: heap::&[[u8]], b: wide::*[[[u16]]], c: heap::&[[u8; 4]],
				d: heap::&S, e: heap::&A,
			) {}
		"});
		let mut case = TestCase::new(&source);
		case.diagnostics().assert_none();
		assert_eq!(param_layout(&mut case, "f", 0), Ok(known(12, 4)));
		assert_eq!(param_layout(&mut case, "f", 1), Ok(known(32, 8)));
		assert_eq!(param_layout(&mut case, "f", 2), Ok(known(8, 4)));
		// A slice or an array: its counts are not known until it is.
		assert_eq!(param_layout(&mut case, "f", 3), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 4), Ok(known(4, 4)));
	}

	#[test]
	fn an_abstract_part_or_a_reference_has_no_layout() {
		let source = with_memories(indoc! {"
			struct Wrap<T>(T);
			func f<T: StackValue, Mem: Memory>(
				a: T, b: Wrap<T>, c: heap::&T, d: Mem::&u8,
				e: func(u32) -> u32, g: (u8, func(u32) -> u32),
			) {}
		"});
		let mut case = TestCase::new(&source);
		case.diagnostics().assert_none();
		assert_eq!(param_layout(&mut case, "f", 0), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 1), Ok(None));
		// An address is as wide as its memory, whatever it points to.
		assert_eq!(param_layout(&mut case, "f", 2), Ok(known(4, 4)));
		assert_eq!(param_layout(&mut case, "f", 3), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 4), Ok(None));
		assert_eq!(param_layout(&mut case, "f", 5), Ok(None));
	}

	/// A sized array is its elements, one after another, aligned as one; an
	/// aggregate holding it gets its bytes but no values, since it is never
	/// one value. A slice or an abstract length has no size.
	#[test]
	fn an_array_field_takes_its_elements_bytes() {
		let source = with_memories(indoc! {"
			#[fixed_order]
			struct Header(len: u8, data: [u16; 3], tail: u32);
			struct Holder<A>(a: A);
			func f(
				a: heap::&Header, b: heap::&[[u8; 2]; 3],
				c: heap::&Holder<[u8]>, d: heap::&Holder<[[u32; 2]; 0]>,
			) {}
		"});
		let mut case = TestCase::new(&source);
		case.diagnostics().assert_none();
		let pointees: Vec<TypeIndex> = (case.param_types("f").to_vec())
			.into_iter()
			.map(|ty| match *case.sema.types.resolve(ty) {
				Type::Pointer { to, .. } => to,
				_ => panic!("a pointer"),
			})
			.collect();
		let index = case
			.sema
			.aggregate_layout(
				&case.strings,
				AssumptionEnvIdx::ROOT,
				pointees[0],
			)
			.unwrap()
			.expect("a laid-out struct");
		// `len` at 0, `data` at 2 (six bytes), `tail` at 8.
		assert_eq!(
			contents(&case, index),
			aggregate(
				(12, 4),
				&[0, 2, 8],
				&[(Primitive::U8, 0), (Primitive::U32, 8)],
			)
		);
		// An array's values are its element's, once per element.
		let (layout, values) = case
			.sema
			.memory_values(&case.strings, AssumptionEnvIdx::ROOT, pointees[1])
			.unwrap()
			.expect("a laid-out array");
		assert_eq!(layout, Layout { size: 6, align: 1 });
		assert_eq!(
			&*values,
			(0..6).map(|at| (Primitive::U8, at)).collect::<Vec<_>>()
		);
		let mut layout = |ty| {
			case.sema
				.memory_layout(&case.strings, AssumptionEnvIdx::ROOT, ty)
		};
		assert_eq!(layout(pointees[2]), Ok(None));
		assert_eq!(layout(pointees[3]), Ok(known(0, 4)));
	}

	#[test]
	fn a_struct_containing_itself_has_no_layout() {
		let source = with_memories(indoc! {"
			struct Selfish(s: Selfish);
			func f(x: Selfish) {}
		"});
		let mut case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::RecursiveTypeWithoutIndirection]);
		assert_eq!(param_layout(&mut case, "f", 0), Err(SolverError::Poisoned));
	}
}
