//! One defined function's graph optimization, independent of module scheduling.

use super::{Locations, Placement, Uses};
use crate::mir::{FunctionId, MIR};

/// Replace one defined function's body with MIR emitted from its value/effect
/// graph. Panics on an imported function or an invalid graph/placement.
///
/// Function identity, signature and module item IDs stay stable. Other bodies
/// are not processed. Emission may append interned multi-result signatures.
/// No module reachability, compaction, inlining or Wasm generation happens here.
pub fn optimize_function(mir: &mut MIR, id: FunctionId) {
	let code = {
		let graph = super::build(mir, id);
		#[cfg(test)]
		graph.verify().expect("well-formed graph");

		// Placement borrows only the graph; discovery/index storage can expire
		// before emission allocates the replacement body.
		let placement = {
			let uses = Uses::collect(&graph);
			let locations = Locations::build(&graph);
			Placement::build(&uses, &locations).expect("valid placement")
		};
		super::emit(mir, id, &placement)
	};
	// All graph and planning storage has expired before replacing the old body.
	#[cfg(test)]
	crate::mir::body::verify(
		&code.body,
		code.root,
		&code.locals,
		code.label_count,
	)
	.expect("emitted MIR has valid ownership, locals and labels");
	*mir.functions[usize::from(id)].code_mut().unwrap() = code;
}
