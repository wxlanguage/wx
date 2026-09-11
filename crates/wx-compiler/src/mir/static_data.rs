use std::collections::HashMap;

use string_interner::symbol::SymbolU32;

use crate::ast;

use super::StaticEntry;

/// Owns static byte entries and the per-memory string deduplication index.
#[derive(Default)]
pub(super) struct StaticDataPool {
	entries: Vec<StaticEntry>,
	strings: HashMap<(SymbolU32, ast::DefId), u32>,
}

impl StaticDataPool {
	pub(super) fn push(
		&mut self,
		bytes: Vec<u8>,
		align: u32,
		memory: ast::DefId,
	) -> (u32, u32) {
		let size = bytes.len() as u32;
		let index = self.entries.len() as u32;
		self.entries.push(StaticEntry {
			bytes: bytes.into_boxed_slice(),
			align,
			memory,
		});
		(index, size)
	}

	pub(super) fn push_string(
		&mut self,
		symbol: SymbolU32,
		bytes: &[u8],
		memory: ast::DefId,
	) -> (u32, u32) {
		if let Some(&index) = self.strings.get(&(symbol, memory)) {
			return (index, self.entries[index as usize].bytes.len() as u32);
		}
		let (index, size) = self.push(bytes.to_vec(), 1, memory);
		self.strings.insert((symbol, memory), index);
		(index, size)
	}

	pub(super) fn finish(self) -> Vec<StaticEntry> {
		self.entries
	}
}
