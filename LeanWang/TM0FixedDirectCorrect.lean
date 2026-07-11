/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FixedDirectProgram
import LeanWang.TM0FoldedCompiler.FoldedTape

/-!
# Correctness of the direct fixed-TM0 program

The direct finite table and the previously certified position-generated table
take the same step on every folded configuration. This lets the direct program
reuse the tape-folding semantic theorem while the shared geometry is split out
of the legacy compiler.
-/

noncomputable section

namespace LeanWang
namespace TM0FixedDirectCorrect

open TM0Route TM0FoldedCompiler TM0FixedDirectProgram

set_option maxRecDepth 20000

theorem nextID_eq_positionProgramData
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    (programWithTable tc (rows tc)).nextID id =
      (positionProgramData tc).nextID id := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  let read := foldedSymbolCode marked left right
  have hread : foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hcell : id.tape id.head = read := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right, read]
  apply PostProgram.nextID_eq_of_state_some_of_steps_eq hstate
  rw [hcell]
  cases hsource : partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
  | none =>
      have hsource' : partrecStartedTM0Machine tc cfg.q
          (foldedRead side left right) = none := by
        simpa [hread] using hsource
      have hdirect := direct_step_eq_none_of_no_source_step
        hq side marked left right hsource'
      have hposition := positionProgramData_step_sim_eq_none_of_no_step
        (tc := tc) (q := cfg.q) (side := side) (marked := marked)
        (left := left) (right := right) hq hsource'
      exact hdirect.trans hposition.symm
  | some next =>
      rcases next with ⟨q', stmt⟩
      have hsource' : partrecStartedTM0Machine tc cfg.q
          (foldedRead side left right) = some (q', stmt) := by
        simpa [hread] using hsource
      have hdirect := direct_step_of_source_step (marked := marked) hq hsource'
      have hposition := positionProgramData_step_sim_of_step
        (marked := marked) hq hsource'
      exact hdirect.trans hposition.symm

end TM0FixedDirectCorrect
end LeanWang
