//! Index newtypes for the compiler's side tables.

/// Declares a `u32` newtype used as an index into one of the compiler's side
/// tables, with the conversions every such index needs.
///
/// Wrapping these instead of passing bare `u32`s is what stops one table's
/// index being used against another, such as a function ID indexing a local
/// table instead of the function table.
macro_rules! index_newtype {
	($(#[$meta:meta])* $field_visibility:vis $name:ident) => {
		$(#[$meta])*
		#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
		#[cfg_attr(any(debug_assertions, test), derive(serde::Serialize))]
		#[cfg_attr(test, derive(PartialOrd, Ord))]
		pub struct $name($field_visibility u32);

		impl $name {
			#[inline]
			pub(crate) fn new(index: u32) -> Self {
				Self(index)
			}
		}

		impl From<$name> for u32 {
			#[inline]
			fn from(index: $name) -> Self {
				index.0
			}
		}

		impl From<$name> for usize {
			#[inline]
			fn from(index: $name) -> Self {
				index.0 as usize
			}
		}
	};
}

pub(crate) use index_newtype;
