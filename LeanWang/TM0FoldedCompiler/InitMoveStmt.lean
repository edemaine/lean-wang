/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.InitMembershipRows

/-!
Local folded-move statement lemmas.
-/

noncomputable section
namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

/-- Side of the folded tape after a simulated TM0 move. -/
theorem foldedMoveNextSide_mem_foldSideList
    (side : FoldSide) (marked : Bool) (dir : Turing.Dir) :
    foldedMoveNextSide side marked dir ∈ foldSideList := by
  exact mem_foldSideList _

/--
Local one-sided command for a simulated TM0 move.

Moving across the origin changes the folded side without moving the local head,
implemented as a no-op write of the current folded cell.
-/
theorem foldedMoveStmt_applyStmt_head
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    (tape : Nat → Nat) (head : Nat) :
    (PostProgram.applyStmt (foldedMoveStmt side marked cell dir) tape head).2 =
      foldedMoveHead side marked head dir := by
  cases side <;> cases marked <;> cases dir <;>
    simp [foldedMoveStmt, foldedMoveHead, PostProgram.applyStmt, Move.apply]

theorem foldedMoveStmt_applyStmt_tape
    (side : FoldSide) (marked : Bool) (cell : Nat) (dir : Turing.Dir)
    {tape : Nat → Nat} {head : Nat} (hcell : tape head = cell) :
    (PostProgram.applyStmt (foldedMoveStmt side marked cell dir) tape head).1 = tape := by
  cases side <;> cases marked <;> cases dir <;>
    simp [foldedMoveStmt, PostProgram.applyStmt, hcell]

end TM0FoldedCompiler

end LeanWang
