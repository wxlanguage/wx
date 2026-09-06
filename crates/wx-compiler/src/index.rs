//! Index newtypes for the compiler's side tables.

/// Declares a `u32` newtype used as an index into one of the compiler's side
/// tables, with the conversions every such index needs.
///
/// Wrapping these instead of passing bare `u32`s is what stops one table's
/// index being used against another. The sharpest case is `mir::PhysIndex` vs
/// `mir::ScalarIndex`: two index spaces over the *same* aggregate that
/// coincide only when it is flat and free of zero-sized fields, so a mix-up
/// compiles fine and silently emits wrong code for everything else.
///
/// Leading attributes are accepted so the generated type can carry its own
/// doc comment:
///
/// ```ignore
/// index_newtype!(
///     /// Index into an aggregate's physical field list.
///     PhysIndex
/// );
/// ```
macro_rules! index_newtype {
	($(#[$meta:meta])* $name:ident) => {
		$(#[$meta])*
		#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
		#[cfg_attr(test, derive(serde::Serialize, PartialOrd, Ord))]
		pub struct $name(u32);

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
