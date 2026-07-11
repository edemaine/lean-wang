/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionCorrect.LocalStep

/-!
Reachability for the position-coded folded simulation from any related
configuration. This module has no dependency on the blank-tape initializer.
-/

noncomputable section

namespace LeanWang
namespace TM0FoldedCompiler

theorem FoldedConfigRel_position_reaches
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg') :
    ∃ n : Nat,
      FoldedConfigRel tc cfg' (Nat.iterate (positionProgramData tc).nextID n id) := by
  induction hreach with
  | refl =>
      exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_position_step hn (by simpa using hstep)

theorem FoldedConfigRel_position_reaches_halt
    {tc : Turing.ToPartrec.Code}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg')
    (hhalt :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none) :
    ∃ n : Nat, (Nat.iterate (positionProgramData tc).nextID n id).state = none := by
  rcases FoldedConfigRel_position_reaches (tc := tc) hrel hreach with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_position_halt_step hn hhalt

end TM0FoldedCompiler
end LeanWang
