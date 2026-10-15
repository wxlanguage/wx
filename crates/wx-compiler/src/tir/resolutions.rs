//! Every written name the compiler resolved, in one table.
//!
//! The caller owns the table next to the diagnostics sink and lends it
//! `&mut` to every stage: phase 1 records the segments of `use` paths, the
//! path walk records every segment it resolves, and signature construction
//! records generic parameters and selected members. Only code that has
//! committed to a meaning records it, so a lookup that is tried and
//! discarded leaves no trace.
//!
//! Entries are keyed by where the name is written, so resolving the same
//! site again overwrites it instead of adding a second entry. The order is
//! by file and then position, which turns "what does the name under the
//! cursor mean" into a range lookup. Who refers to a definition, or which
//! `use` items are never used, is the inverse of this table and is computed
//! from it when needed.

use std::collections::BTreeMap;

use super::defs::{DefKey, MemberKind, Tier, UseItemIndex};
use super::types::TypeEnvIdx;
use crate::diagnostics::SourceSpan;

/// Keyed by the written name's span and the tier it was looked up in: a
/// `use` leaf names a type and a value at the same span.
#[derive(Default)]
pub(super) struct NameResolutions {
	pub(super) by_site: BTreeMap<(SourceSpan, Tier), Referent>,
}

/// What a written name refers to.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(debug_assertions, derive(Debug))]
pub(super) enum Referent {
	/// A definition declared in the namespace the name was looked up in:
	/// an item, a module, a package or an import block.
	Definition(DefKey),
	/// A definition the namespace it was looked up in made visible through
	/// a `use` item there, a named import or a glob. Only that first `use`
	/// is recorded; one it leads through in another namespace can be found
	/// again by looking the name up from it.
	Import {
		definition: DefKey,
		import: UseItemIndex,
	},
	/// A generic parameter or `Self`: its frame and position in it.
	TypeParam { env: TypeEnvIdx, index: u32 },
	/// A member selected through a type: `T::A`, `<X as Tr>::A`.
	Member(MemberKind),
}

impl Referent {
	/// What a namespace lookup found: `import` is the `use` item it came
	/// through, as `BindingLookup::Found` reports it.
	pub(super) fn from_lookup(
		definition: DefKey,
		import: Option<UseItemIndex>,
	) -> Self {
		match import {
			Some(import) => Self::Import { definition, import },
			None => Self::Definition(definition),
		}
	}
}
