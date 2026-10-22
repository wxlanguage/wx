//! Distinct lookup candidates, retained in discovery order.
//!
//! The first candidate stays inline; collection storage allocates only when
//! a second distinct candidate is discovered. Keys describe lookup identity,
//! independently of the resolved payload.

pub(super) struct CandidateSet<K, T> {
	first: Option<(K, T)>,
	additional: Vec<(K, T)>,
}

pub(super) enum CandidateSelection<T> {
	None,
	One(T),
	Many(Vec<T>),
}

impl<K: PartialEq, T> CandidateSet<K, T> {
	pub(super) fn new() -> Self {
		Self {
			first: None,
			additional: Vec::new(),
		}
	}

	pub(super) fn insert(&mut self, key: K, value: T) {
		if self
			.first
			.iter()
			.chain(self.additional.iter())
			.any(|(seen, _)| *seen == key)
		{
			return;
		}
		if self.first.is_none() {
			self.first = Some((key, value));
		} else {
			self.additional.push((key, value));
		}
	}

	pub(super) fn finish(self) -> CandidateSelection<T> {
		match self.first {
			None => CandidateSelection::None,
			Some((_, first)) if self.additional.is_empty() => {
				CandidateSelection::One(first)
			}
			Some((_, first)) => CandidateSelection::Many(
				std::iter::once(first)
					.chain(self.additional.into_iter().map(|(_, value)| value))
					.collect(),
			),
		}
	}
}
