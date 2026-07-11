/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionCorrect.ReachCore

/-!
Reflection of position-coded machine halting back to TM0, from any related
configuration. This module has no dependency on the blank-tape initializer.
-/

noncomputable section

namespace LeanWang
namespace TM0FoldedCompiler

theorem tm0_reaches_halt_of_positionProgramData_halts
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∀ n : Nat,
      (Nat.iterate (positionProgramData tc).nextID n id).state = none →
        ∃ cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc),
          StateTransition.Reaches
            (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg' ∧
          Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none
  | 0, hhalt => by
      rcases hrel with ⟨side, _hq, hstate, _htape⟩
      simp [hstate] at hhalt
  | n + 1, hhalt => by
      cases hstep :
          Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg with
      | none =>
          exact ⟨cfg, Relation.ReflTransGen.refl, hstep⟩
      | some cfg₁ =>
          have hrel₁ := FoldedConfigRel_position_step hrel hstep
          have hhalt₁ :
              (Nat.iterate (positionProgramData tc).nextID n
                  ((positionProgramData tc).nextID id)).state =
                none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_positionProgramData_halts hrel₁ n hhalt₁ with
            ⟨cfg', hreach, hterminal⟩
          refine ⟨cfg', ?_, hterminal⟩
          exact Relation.ReflTransGen.head (by simpa using hstep) hreach

end TM0FoldedCompiler
end LeanWang
