//! Optimize reached functions before discovering their module dependencies.
//! IDs stay stable; the returned marks select items for codegen.

use crate::mir::references::Reference;
use crate::mir::{FunctionId, Item, MIR};

/// Items reached from exports and start across the whole MIR program destined
/// for one Wasm output, not a source file or namespace. These dense columns use
/// existing item IDs; they do not borrow or retain bodies. Further body/root
/// changes can invalidate the result.
pub struct Reachability {
	functions: Vec<bool>,
	globals: Vec<bool>,
	memories: Vec<bool>,
	data: Vec<bool>,
}

impl Reachability {
	fn empty(mir: &MIR) -> Self {
		Self {
			functions: vec![false; mir.functions.len()],
			globals: vec![false; mir.globals.len()],
			memories: vec![false; mir.memories.len()],
			data: vec![false; mir.static_entries.len()],
		}
	}

	/// Retain references in original MIR for the direct execution oracle.
	#[cfg(test)]
	pub(crate) fn collect_for_tests(mir: &MIR) -> Self {
		let mut reached = Self::empty(mir);
		let mut pending = Vec::new();
		mir.roots(|reference| reached.enqueue(reference, &mut pending));
		while let Some(reference) = pending.pop() {
			mir.dependencies(reference, |dependency| {
				reached.enqueue(dependency, &mut pending)
			});
		}
		reached
	}

	pub fn is_reachable(&self, reference: Reference) -> bool {
		match reference {
			Reference::Item(Item::Function(id)) => {
				self.functions[usize::from(id)]
			}
			Reference::Item(Item::Global(id)) => self.globals[usize::from(id)],
			Reference::Item(Item::Memory(id)) => self.memories[usize::from(id)],
			Reference::Data(id) => self.data[usize::from(id)],
		}
	}

	fn enqueue(&mut self, reference: Reference, pending: &mut Vec<Reference>) {
		let marked = match reference {
			Reference::Item(Item::Function(id)) => {
				&mut self.functions[usize::from(id)]
			}
			Reference::Item(Item::Global(id)) => {
				&mut self.globals[usize::from(id)]
			}
			Reference::Item(Item::Memory(id)) => {
				&mut self.memories[usize::from(id)]
			}
			Reference::Data(id) => &mut self.data[usize::from(id)],
		};
		if !*marked {
			*marked = true;
			pending.push(reference);
		}
	}
}

/// Starting at exports and start, optimize each reached defined function once,
/// then follow references in its replacement body. Imports are reached items,
/// but have no bodies to optimize. Unreached bodies remain untouched.
///
/// No items are deleted or renumbered. Only function bodies and (through type
/// interning) signatures may change. Codegen must use the returned marks to
/// select output items; the MIR tables still contain unreachable entries.
pub fn optimize_reachable(mir: &mut MIR) -> Reachability {
	discover(mir, super::optimize_function)
}

// Keeping the body operation separate also lets tests record exactly which
// functions are processed while running the real function optimizer.
fn discover(
	mir: &mut MIR,
	mut optimize: impl FnMut(&mut MIR, FunctionId),
) -> Reachability {
	let mut reached = Reachability::empty(mir);
	let mut pending = Vec::new();
	mir.roots(|reference| reached.enqueue(reference, &mut pending));
	while let Some(reference) = pending.pop() {
		if let Reference::Item(Item::Function(id)) = reference
			&& mir.function(id).code().is_some()
		{
			optimize(mir, id);
		}
		mir.dependencies(reference, |dependency| {
			reached.enqueue(dependency, &mut pending);
		});
	}
	reached
}

#[cfg(test)]
mod tests;
