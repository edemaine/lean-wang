/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FixedDirectGeometry

/-!
# Exact execution equations for the direct folded program

These equations isolate finite-table lookup and Post-machine record reduction
from the folded-tape invariant proofs.
-/

namespace LeanWang
namespace TM0FixedDirectExecution

open TM0Route TM0FoldedCompiler TM0FixedDirectProgram TM0FixedDirectGeometry

theorem nextID_write
    {tc : Turing.ToPartrec.Code} {q q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right new : SourceSymbol}
    {id : PostID}
    (hstate : id.state = some (foldedSimStateCode tc side q))
    (hcell : id.tape id.head = foldedSymbolCode marked left right)
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) =
      some (q', Turing.TM0.Stmt.write new)) :
    (program tc).nextID id =
      { tape := Function.update id.tape id.head
          (foldedWriteForStmt side marked new left right)
        head := id.head
        state := some (foldedSimStateCode tc side q') } := by
  change (programWithTable tc (rows tc)).nextID id = _
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [direct_step_of_source_step (marked := marked) hq hstep]
  rfl

theorem nextID_move
    {tc : Turing.ToPartrec.Code} {q q' : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {dir : Turing.Dir} {id : PostID}
    (hstate : id.state = some (foldedSimStateCode tc side q))
    (hcell : id.tape id.head = foldedSymbolCode marked left right)
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) =
      some (q', Turing.TM0.Stmt.move dir)) :
    (program tc).nextID id =
      { tape := id.tape
        head := foldedMoveHead side marked id.head dir
        state := some (foldedSimStateCode tc
          (foldedMoveNextSide side marked dir) q') } := by
  change (programWithTable tc (rows tc)).nextID id = _
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [direct_step_of_source_step (marked := marked) hq hstep]
  cases side <;> cases marked <;> cases dir <;>
    simp [simRowOfStep, mkRow, foldedMoveStmt, foldedMoveHead,
      foldedMoveNextSide, PostProgram.applyStmt, Move.apply, hcell]

theorem nextID_halt
    {tc : Turing.ToPartrec.Code} {q : SourceLabel tc}
    {side : FoldSide} {marked : Bool} {left right : SourceSymbol}
    {id : PostID}
    (hstate : id.state = some (foldedSimStateCode tc side q))
    (hcell : id.tape id.head = foldedSymbolCode marked left right)
    (hq : q ∈ partrecStartedTM0LabelList tc)
    (hstep : partrecStartedTM0Machine tc q (foldedRead side left right) = none) :
    ((program tc).nextID id).state = none := by
  change ((programWithTable tc (rows tc)).nextID id).state = none
  rw [PostProgram.nextID_of_running hstate, hcell]
  rw [direct_step_eq_none_of_no_source_step hq side marked left right hstep]

end TM0FixedDirectExecution
end LeanWang
