//! MIR's one table of type lists: signatures, Wasm's function types. An
//! entry is its parameters and then its results, every one a scalar, as one
//! run of a shared column. A function's type is one; so is a multi-result
//! type ([`ValueType::Aggregate`]), with no parameters, as a Wasm block
//! yielding several values is typed by a signature `[] -> [t*]`.
//!
//! The table is interned by content, so equal lists are one entry and two
//! source types with the same scalars are one MIR type.

use std::hash::BuildHasher;

use hashbrown::HashTable;
use rustc_hash::FxBuildHasher;

use super::{SignatureIndex, ValueType};

/// One entry: `len` items of the column from `start`, the first `params`
/// of them its parameters, the rest its results.
#[derive(Clone, Copy)]
struct Signature {
	start: u32,
	params: u32,
	len: u32,
}

#[derive(Default)]
pub struct Signatures {
	entries: Vec<Signature>,
	items: Vec<ValueType>,
	/// Every entry, by the hash of its parameters and results, which are
	/// compared in place in `items`.
	lookup: HashTable<SignatureIndex>,
	hasher: FxBuildHasher,
}

impl Signatures {
	/// The signature `params -> results`, every item a scalar.
	pub(crate) fn intern(
		&mut self,
		params: &[ValueType],
		results: &[ValueType],
	) -> SignatureIndex {
		debug_assert!(
			params.iter().chain(results).all(|ty| ty.is_scalar()),
			"a signature's items are scalars"
		);
		let hash = self.hasher.hash_one((params, results));
		let Self {
			entries,
			items,
			lookup,
			hasher,
		} = self;
		if let Some(&index) = lookup.find(hash, |&index| {
			contents(entries[usize::from(index)], items) == (params, results)
		}) {
			return index;
		}
		let index = SignatureIndex::new(u32::try_from(entries.len()).unwrap());
		entries.push(Signature {
			start: u32::try_from(items.len()).unwrap(),
			params: u32::try_from(params.len()).unwrap(),
			len: u32::try_from(params.len() + results.len()).unwrap(),
		});
		items.extend_from_slice(params);
		items.extend_from_slice(results);
		lookup.insert_unique(hash, index, |&index| {
			hasher.hash_one(contents(entries[usize::from(index)], items))
		});
		index
	}

	/// The type of several scalars as one value: one scalar is that scalar,
	/// none is `Unit`.
	pub(crate) fn value_of(&mut self, scalars: &[ValueType]) -> ValueType {
		match *scalars {
			[] => ValueType::Unit,
			[scalar] => scalar,
			_ => ValueType::Aggregate {
				signature: self.intern(&[], scalars),
			},
		}
	}

	pub fn params(&self, at: SignatureIndex) -> &[ValueType] {
		contents(self.entries[usize::from(at)], &self.items).0
	}

	pub fn results(&self, at: SignatureIndex) -> &[ValueType] {
		contents(self.entries[usize::from(at)], &self.items).1
	}

	/// The scalars a value of `ty` is, in order: none for a zero-sized or a
	/// diverging one.
	pub fn scalars<'a>(&'a self, ty: &'a ValueType) -> &'a [ValueType] {
		match ty {
			ValueType::Unit | ValueType::Never => &[],
			ValueType::Aggregate { signature } => {
				debug_assert!(
					self.params(*signature).is_empty(),
					"a multi-result type has no parameters"
				);
				self.results(*signature)
			}
			scalar => std::slice::from_ref(scalar),
		}
	}
}

/// What an entry is compared and hashed by: its parameters and its
/// results, read from the column.
fn contents(
	entry: Signature,
	items: &[ValueType],
) -> (&[ValueType], &[ValueType]) {
	let items = &items[entry.start as usize..][..entry.len as usize];
	items.split_at(entry.params as usize)
}
