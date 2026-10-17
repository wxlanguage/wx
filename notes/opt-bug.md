Here's the exact mechanism. It's a bug in how the inliner models return, colliding with an assumption in the sea-of-nodes builder.

The chain

1. How return normally works. MIR has ExprKind::Return { value }. When a function is compiled on its own, opt/builder.rs handles it at build_expr → ExprKind::Return arm (builder.rs:659): merge the value into blocks[0].result (the function block, created eagerly at builder.rs:103) and emit ControlNode::Return. Works fine — this is why standalone clamp compiles.

2. What the inliner does to return. mir/inlining.rs::inline_call splices the callee body in as an ExprKind::Block { scope_index: wrapper_scope, … }, where wrapper_scope is a fresh scope with kind: tir::BlockKind::Block (inlining.rs:335). Then Rebaser (inlining.rs:135) rewrites every ExprKind::Return { value } in the callee into ExprKind::Break { scope_index: wrapper_scope, value } — "return" becomes "break out of the wrapper block".

3. Why that break has no valid target. In opt/builder.rs, loop-ness is tracked entirely by blocks[idx].loop_index — nothing ever reads BlockKind. The handlers that register a blocks[scope] entry are build_loop (with loop_index: Some), build_if_else, build_switch_arm. But build_block_expr (builder.rs:953), the handler for a plain ExprKind::Block, registers nothing — it just emits the block's statements into the enclosing block_idx and leaves blocks[scope_index] == None. A plain block is transparent to the builder. That's safe under normal lowering because nothing is ever a break target except loops (labeled blocks like outer: { break :outer } are lowered to a non-repeating ExprKind::Loop, not ExprKind::Block).

4. The panic. The inlined body now contains Break { scope_index: wrapper_scope } whose target is a plain block the builder never registered. build_expr's ExprKind::Break arm (builder.rs:729) is written exclusively for loop ta

let target = u32::from(           //wrapper_scope
let loop_param_updates target, …); // ← boom

loop_param_updates (builoop_data(target) →self.blocks[target].as_ref().unwrap() → None.unwrap() at opt/mod.rs:823.

Even if that slot were populated, the very next line inside loop_data is
.loop_index.expect("loop block") — a wrapperblock has loop_index: None, so it would still blow up. The Break arm
assumes every break com and feeds a loop'sbreak-result phi; there is no "break to an ordinary block" path.

Why min/max are fine but clamp isn't

┌────────────┬──────────────────────────────┬─────────────────────────┐
│   method   │         s ExprKind::Return?  │
├────────────┼──────────────────────────────┼─────────────────────────┤
│ Ord::min   │ if self — it's an            │
│            │ else { other }               │ if-expression           │
├────────────┼──────────────────────────────┤

┌────────────┬──────────────────────────────┬─────────────────────────┐
│   method   │             body             │  has ExprKind::Return?  │
├────────────┼──────────────────────────────┼─────────────────────────┤
│ Ord::min   │ if self < other { self }     │ no — it's an            │
│            │ else { other }               │ if-expression           │
├────────────┼──────────────────────────────┤
│ Ord::max   │ if self < other { other }    │ no                      │
│            │ else { s                     │
├────────────┼──────────────────────────────┼─────────────────────────┤
│            │ if max < — two               │
│ Ord::clamp │ }; if self < min { return    │ statement-positio│            │ min }; ily returns           │
│            │ return max }; self           │                  └────────────┴──────────────────────────────┘
The inliner's Return → te only fires when thebody actually contains ExprKind::Return. min/max produce none, wrapper block stays an ld_block_expr harmlesslyskips it. clamp's two early returns each become a Break to the unregistered wrapper scanics.

All the RawPtr methods s too — no return — which is why every one of them inlines cleanly.                          
Where the defect lives                                             
mir/inlining.rs: it assumes "return ⇒ break out of a wrapper block,opt/builder.rs has no cn-loop block. Real fixes, cleanest first:                                                    
1. Keep inlined Return as ExprKind::Return when the call is in tail   position (no code fock) — then the existingReturn arm handles it. Doesn't cover mid-body early returns.    2. Teach opt/builder.rs: have build_block_exprregister blocks[scope_index] (with loop_index: None), and branch   Break arm on loop_int path; block target →merge into that block's result, emit a block-break control node,   loop_param_updates. real labeled-blocksupport would need.                                             3. Full labeled-block sh inlined return lowering to it.                                                          loop_param_updates. This is also exactly what real labeled-block support would need.
3. Full labeled-block support in the builder, with inlined return lowering to it.                                                          
Nothing is applied — std/main.wx is back at your WIP baseline, my  #[inline] set is parkednes.wx, andtarget/release/wx is rebuilt to match the restored tree.           
✻ Brewed for 3m 4s                                                   
❯ so where the problem is exactly? in mir or opt?                    
The defect is in MIR — specifically mir/inlining.rs.               
The inliner is the only thing in the whole compiler that produces  ExprKind::Break targetik scope. Every Break that normal TIR→MIR lowering emits targets a Loop scope (labeled blocks included — outer: { bren-repeatingExprKind::Loop, not ExprKind::Block). So opt/builder.rs was written to a real invariant that helr seen: break target ⇒loop. The inliner quietly broke that invariant by inventing a new
convention ("rewrite Re wrapper Block") andnever teaching the downstream consumer about it.

opt has a latent gap (no "break to an ordinary block" path), but that gap
is unreachable except tpt already handlesExprKind::Return correctly on its own — the inliner chose to rewrite
Return into an unsuppore it alone or use aloop-shaped scope.

So:
- Bug owner: mir/inlinick, which is not validMIR by the de-facto contract.
- Smallest fix: in the on Return as Return, ormake wrapper_scope loop-shaped so the existing loop-break path handles
  it. Zero opt changes.
- Better long-term fix: in opt — give build_block_expr a registered
  blocks[] entry and br_index, which also getsyou proper labeled-block codegen. But that's an enhancement, not where
  the bug is.

✻ Cooked for 19s

❯ I think we just need topiler, secificallyoptimizer to recognize the break from block, cause this is how wasm works
  and replacing it with lng to do. I don'treally understand why are you suggesting to fix MIR

  Ran 2 shell commands

You're right, and my "fix MIR" framing was wrong. Let me correct it.   
The inliner's Return → Break(wrapper_block) is the correct lowering.   WASM's block + br is a hat's exactly return from an inlined body, or a labeled-block break, or any early-exit merge.    Faking it as a Loop wou scheduler's looptail-code (back-edge + loop-param commit), and to any future loop pass.The wrapper genuinely i
And ExprKind::Break-to-egitimate MIR — labeledblocks (outer: { break :outer }) are a real language feature. opt just never implemented that ing happens to routelabeled blocks through BlockKind::Loop scopes today, so no input ever exercised it. The inlinitimate producer of theshape. That's an opt gap, not an inliner bug.

What needs to change, all in opt                                          
The primitive is already there — the scheduler wraps loops in             truction::Block so b19), and does the samefor br_table. It just needs to be reachable for a plain scope.            
1. BlockScope already carries kind: BlockKind (Block | Loop) and the      inliner sets Block o tell them apartdirectly, not just via loop_index.                                     build_block_expr (busparent (registers noblocks[] entry, emits into the parent block_idx). When the scope is a  break target: registock { loop_index: None,result: <scope ty>, … }), build statements into it, finalize result =  fallthrough merged wy build_loop minusloop-params and the back-edge. Normal {} blocks are never targeted, so their output stays b
3. build_expr ExprKind::Break arm (builder.rs:729) — branch on target      loop_index:
   - Some → current loop path (loop_param_updates, break_result_outputs,     back-edge).
   - None → merge value into blocks[target].result (reuse the merge_values   / phi-set machinerk with emptyloop_param_updates, and skip loop_param_updates() entirely — there      are no loop-carrieindings already flowthrough.                                                              Scheduler — emit a bd around a targetednon-loop scope (generalize the existing loop-wrapping at                scheduler.rs:419). Cth) handling(scheduler.rs:453) already computes branch depth generically, so it     works once the enclo
5. liveness.rs:35 and other func.blocks[idx].unwrap() sites fix themselves once the block scope

loop_data / loop_param_-only — they're justnever called on the block-break path.

Here's another agent review of this with recommendations:

The agent’s final direction is sensible, but I wouldn’t accept its implementation plan as complete. I checked the current code: the mismatch is real, and several claims in the proposal are too confident.
The inliner rewrites returns into breaks targeting a plain wrapper block. Meanwhile, [the optimizer’s builder (line 730)](/Users/melkam/Desktop/wx/crates/wx-compiler/src/opt/builder.rs:730) assumes every break targets a loop, and ordinary blocks aren’t registered as targets. Supporting explicit block exits is a clean solution.
Here’s what I would correct:
- “Keep Return when no code follows” is unsafe as stated. Last in a block doesn’t necessarily mean returning directly from the caller. In return inline_call() + 1, a return inside the expanded call must still allow the addition. That shortcut requires proving true function-tail position.
- “Ordinary SSA bindings already flow through” overlooks exit merging. For general block support, mutations to outer locals must be merged across every break and reachable fallthrough. Imagine a block that sets x = 1 and breaks on one path, but sets x = 2 on another: code after the block must see the corresponding value. Merging only the block’s result is insufficient.
- The scheduler’s break handling isn’t generic yet. Its [Break arm (line 453)](/Users/melkam/Desktop/wx/crates/wx-compiler/src/opt/scheduler.rs:453) explicitly reads loop_data(target).break_result_outputs. The depth calculation looks reusable, but result handling needs restructuring.
- Liveness won’t “fix itself.” A new structured block control node needs explicit traversal in liveness and the scheduler’s other control-flow walks.
- Choose one result convention. Existing loop exits use locals and an empty Wasm block type. The proposal mixes that approach with block <result_ty>. Either can work, but the implementation must consistently deliver values on every exit.
My suggestion is to keep the inliner’s return-to-wrapper-break lowering and implement a first-class breakable block in the optimizer:
1. Add an explicit block control node and shared exit-result bookkeeping; keep loop-carried state loop-specific.
2. Merge block results—and any outer bindings needed afterward—from breaks and reachable fallthrough.
3. Update scheduling, liveness, and control-flow traversal together. Preserve transparent handling for blocks that aren’t break targets.
4. Add execution regressions covering early returns plus fallthrough, calls inside larger expressions, nested loops/blocks, aggregate results, and outer-local mutations.
I’d also add an invariant check that every break targets a supported enclosing scope.
So I agree with the destination, but not the claim that this is mostly registration plus a few branches. The important work is modeling the exit join correctly. Whether you call the original defect “MIR” or “opt” matters less than making that contract explicit.
This assessment is based on source inspection; I haven’t applied or tested a fix.