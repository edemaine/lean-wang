/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.LocalStep

/-!
Finite reachability for the position-coded folded program with an
input-dependent initialization prefix.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

theorem FoldedConfigRel_input_reaches
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg') :
    ∃ n : Nat,
      FoldedConfigRel tc cfg'
        (Nat.iterate (positionProgramDataOnInput tc input).nextID n id) := by
  induction hreach with
  | refl =>
      exact ⟨0, hrel⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact FoldedConfigRel_input_step hn (by simpa using hstep)

theorem FoldedConfigRel_input_reaches_halt
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {cfg cfg' : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id)
    (hreach :
      StateTransition.Reaches
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)) cfg cfg')
    (hhalt :
      Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc) cfg' = none) :
    ∃ n : Nat,
      (Nat.iterate (positionProgramDataOnInput tc input).nextID n id).state = none := by
  rcases FoldedConfigRel_input_reaches (tc := tc) (input := input) hrel hreach with
    ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact FoldedConfigRel_input_halt_step hn hhalt

end TM0FoldedCompiler

end LeanWang
