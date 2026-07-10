/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.WriteMove

/-!
Single-step simulation for the position-coded folded program with an
input-dependent initialization prefix.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

theorem FoldedConfigRel_input_step
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = some cfg') :
    FoldedConfigRel tc cfg' ((positionProgramDataOnInput tc input).nextID id) := by
  cases hM :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
  | none =>
      simp [Turing.TM0.step, hM] at hstep
  | some next =>
      rcases next with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          have hcfg' : cfg' = { q := q', Tape := cfg.Tape.move dir } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_input_move_step
            (tc := tc) (input := input) (cfg := cfg) (id := id)
            (q' := q') (dir := dir) hrel hM
      | write new =>
          have hcfg' : cfg' = { q := q', Tape := cfg.Tape.write new } := by
            simpa [Turing.TM0.step, hM] using hstep.symm
          subst cfg'
          exact FoldedConfigRel_input_write_step
            (tc := tc) (input := input) (cfg := cfg) (id := id)
            (q' := q') (new := new) hrel hM

theorem FoldedConfigRel_input_halt_step
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hstep :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg = none) :
    ((positionProgramDataOnInput tc input).nextID id).state = none := by
  rcases hrel with ⟨side, hq, hstate, htape⟩
  let marked := decide (id.head = 0)
  let left := cfg.Tape.nth (sourceOffset side id.head (leftAbs id.head))
  let right := cfg.Tape.nth (sourceOffset side id.head (rightAbs id.head))
  let read := foldedSymbolCode marked left right
  have hread :
      foldedRead side left right = cfg.Tape.head := by
    unfold left right
    exact foldedRead_active_cell cfg.Tape side id.head
  have hmachine :
      TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head = none := by
    cases hM : TM0Route.partrecStartedTM0Machine tc cfg.q cfg.Tape.head with
    | none => simp
    | some next =>
        simp [Turing.TM0.step, hM] at hstep
  have hmachine' :
      TM0Route.partrecStartedTM0Machine tc cfg.q (foldedRead side left right) =
        none := by
    simpa [hread] using hmachine
  have hcell : id.tape id.head = read := by
    rw [htape id.head]
    simp [foldedCellOfTapeAt, marked, left, right, read]
  have hprogramStep := positionProgramDataOnInput_step_sim_eq_none_of_no_step
    (tc := tc) (input := input) (q := cfg.q) (side := side) (marked := marked)
    (left := left) (right := right) hq hmachine'
  simp [PostProgram.nextID, hstate, hcell, hprogramStep, read]

end TM0FoldedCompiler

end LeanWang
