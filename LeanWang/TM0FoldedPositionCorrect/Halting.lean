/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedPositionCorrect.Step

/-!
Halting equivalences for the generated position-coded folded program.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

theorem positionProgramData_haltsEmpty_of_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
      TM0Route.partrecStartedTM0Input).Dom →
      (positionProgramData tc).HaltsEmpty := by
  intro hdomEval
  let step :=
    Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
  let initCfg :=
    Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input
  have hdomState : (StateTransition.eval step initCfg).Dom := by
    dsimp [step, initCfg] at *
    rw [Turing.TM0.eval] at hdomEval
    exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
      (StateTransition.eval
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
        (Turing.TM0.init (Λ := SourceLabel tc)
          TM0Route.partrecStartedTM0Input))).1 hdomEval
  let haltCfg := (StateTransition.eval step initCfg).get hdomState
  have hmem : haltCfg ∈ StateTransition.eval step initCfg :=
    Part.get_mem hdomState
  rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hhalt⟩
  rcases FoldedConfigRel_position_reaches_halt
      (tc := tc) (cfg := initCfg) (cfg' := haltCfg)
      (id := (positionProgramData tc).runEmpty 2)
      (FoldedConfigRel_position_runEmpty_two tc) hreach hhalt with
    ⟨n, hn⟩
  refine ⟨n + 2, ?_⟩
  rw [positionProgramData_runEmpty_add_two]
  exact hn

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

theorem tm0_eval_dom_of_positionProgramData_haltsEmpty
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).HaltsEmpty →
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  rintro ⟨k, hhalt⟩
  cases k with
  | zero =>
      simp [PostProgram.runEmpty_zero, PostProgram.initialID] at hhalt
  | succ k =>
      cases k with
      | zero =>
          rw [show 1 = 1 by rfl, positionProgramData_runEmpty_one] at hhalt
          simp at hhalt
      | succ n =>
          have hhalt' : ((positionProgramData tc).runEmpty (n + 2)).state = none := by
            rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
            exact hhalt
          have hhaltIter :
              (Nat.iterate (positionProgramData tc).nextID n
                  ((positionProgramData tc).runEmpty 2)).state =
                none := by
            rw [positionProgramData_runEmpty_add_two] at hhalt'
            exact hhalt'
          let step :=
            Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
          let initCfg :=
            Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input
          rcases tm0_reaches_halt_of_positionProgramData_halts
              (tc := tc) (cfg := initCfg) (id := (positionProgramData tc).runEmpty 2)
              (FoldedConfigRel_position_runEmpty_two tc) n hhaltIter with
            ⟨cfg', hreach, hterminal⟩
          have hmem : cfg' ∈ StateTransition.eval step initCfg := by
            exact StateTransition.mem_eval.2 ⟨hreach, hterminal⟩
          have hdomState : (StateTransition.eval step initCfg).Dom :=
            Part.dom_iff_mem.2 ⟨cfg', hmem⟩
          rw [Turing.TM0.eval]
          exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
            (StateTransition.eval
              (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
              (Turing.TM0.init (Λ := SourceLabel tc)
                TM0Route.partrecStartedTM0Input))).2 hdomState

theorem positionProgramData_haltsEmpty_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).HaltsEmpty ↔
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  exact ⟨tm0_eval_dom_of_positionProgramData_haltsEmpty tc,
    positionProgramData_haltsEmpty_of_tm0_eval_dom tc⟩

theorem positionProgramData_haltsEmpty_iff_partrec_eval_dom
    (tc : Turing.ToPartrec.Code) :
    (positionProgramData tc).HaltsEmpty ↔
      (StateTransition.eval
        (Turing.TM2.step TM0Route.partrecTM2)
        (TM0Route.partrecInit tc)).Dom := by
  exact (positionProgramData_haltsEmpty_iff_tm0_eval_dom tc).trans
    ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2 tc).trans
      (TM0Route.partrecStartedTM2_eval_dom_iff_partrec tc))

end TM0FoldedCompiler

end LeanWang
