//! Test-only support code.
//!
//! Split in two: the [`serialize_sorted_map`] helper below is referenced by
//! `serde` attributes on IR types and exists to make snapshot output
//! deterministic, while [`diagnostics`] carries the assertion vocabulary the
//! test suites share.

mod diagnostics;

pub use diagnostics::DiagnosticView;

use std::collections::HashMap;

/// Serializes a HashMap with keys sorted for deterministic snapshot output.
pub fn serialize_sorted_map<K, V, S>(
	map: &HashMap<K, V>,
	serializer: S,
) -> Result<S::Ok, S::Error>
where
	K: Ord + serde::Serialize,
	V: serde::Serialize,
	S: serde::Serializer,
{
	use serde::ser::SerializeMap;
	let mut pairs: Vec<_> = map.iter().collect();
	pairs.sort_by_key(|(k, _)| *k);
	let mut ser = serializer.serialize_map(Some(pairs.len()))?;
	for (k, v) in pairs {
		ser.serialize_entry(k, v)?;
	}
	ser.end()
}
