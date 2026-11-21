/// A non-empty list that stores its first item inline and allocates only when
/// a second item is added.
pub(crate) enum SmallVec<T: Copy> {
	One(T),
	Many(Vec<T>),
}

impl<T: Copy> SmallVec<T> {
	pub(crate) fn new(item: T) -> Self {
		Self::One(item)
	}

	pub(crate) fn push(&mut self, item: T) {
		match self {
			Self::One(first) => {
				*self = Self::Many(vec![*first, item]);
			}
			Self::Many(items) => items.push(item),
		}
	}
}

impl<'a, T: Copy> IntoIterator for &'a SmallVec<T> {
	type Item = T;
	type IntoIter = std::iter::Copied<std::slice::Iter<'a, T>>;

	fn into_iter(self) -> Self::IntoIter {
		match self {
			SmallVec::One(item) => std::slice::from_ref(item),
			SmallVec::Many(items) => items,
		}
		.iter()
		.copied()
	}
}

impl<'a, T: Copy> IntoIterator for &'a mut SmallVec<T> {
	type Item = &'a mut T;
	type IntoIter = std::slice::IterMut<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		match self {
			SmallVec::One(item) => std::slice::from_mut(item),
			SmallVec::Many(items) => items,
		}
		.iter_mut()
	}
}

#[cfg(test)]
mod tests {
	use super::SmallVec;

	#[test]
	fn stores_one_item_inline_and_promotes_on_push() {
		let mut items = SmallVec::new(1);
		assert_eq!((&items).into_iter().collect::<Vec<_>>(), [1]);

		items.push(2);
		items.push(3);
		assert_eq!((&items).into_iter().collect::<Vec<_>>(), [1, 2, 3]);
	}
}
