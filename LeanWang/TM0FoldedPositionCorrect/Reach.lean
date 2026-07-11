/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedGeneratedInit
import LeanWang.TM0FoldedPositionCorrect.ReachCore

/-!
Reachability consequences for the generated position-coded folded program.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

theorem FoldedConfigRel_position_runEmpty_two (tc : Turing.ToPartrec.Code) :
    FoldedConfigRel tc
      (Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input)
      ((positionProgramData tc).runEmpty 2) := by
  rw [positionProgramData_runEmpty_two]
  refine ⟨FoldSide.right, ?_, ?_, ?_⟩
  · simpa [Turing.TM0.init] using default_mem_partrecStartedTM0LabelList tc
  · simp [foldedSimStartState, foldedSimStartStateCode, foldedSimStateCode,
      foldedSimStateOfCode, TM0Route.partrecStartedTM0Start,
      TM0FiniteCompiler.stateCode_default tc, Turing.TM0.init]
  · exact FoldedTapeRel_init_right_zero tc

end TM0FoldedCompiler

end LeanWang
