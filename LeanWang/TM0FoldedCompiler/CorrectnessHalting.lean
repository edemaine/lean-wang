/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedCompiler.FoldedTape
import LeanWang.TM0FoldedCompiler.ProgramRunEmptyTwo

/-!
Halting equivalence for the folded finite one-sided TM0 program.
-/

namespace LeanWang

namespace TM0FoldedCompiler

open TM0Route

theorem foldedCellOfTapeAt_init_right_zero (tc : Turing.ToPartrec.Code) (i : Nat) :
    foldedCellOfTapeAt
        (Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input).Tape
        FoldSide.right 0 i =
      (Function.update (fun _ => foldedBlank) 0
        (foldedOriginSymbol (inputSymbol 0))) i := by
  cases i with
  | zero =>
      have hleft : sourceOffset FoldSide.right 0 (leftAbs 0) = Int.negSucc 0 := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
      have hright : sourceOffset FoldSide.right 0 (rightAbs 0) = 0 := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      simp [foldedOriginSymbol, inputSymbol,
        TM0Route.partrecStartedTM0Input, TM0Route.partrecStartedTM2Input,
        Turing.TM2to1.trInit, Turing.PartrecToTM2.trList,
        Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk',
        Turing.Tape.nth]
  | succ i =>
      have hleft :
          sourceOffset FoldSide.right 0 (leftAbs (Nat.succ i)) =
            Int.negSucc (i + 1) := by
        simp [sourceOffset, activeAbs, leftAbs, rightAbs]
        omega
      have hright :
          sourceOffset FoldSide.right 0 (rightAbs (Nat.succ i)) =
            Int.ofNat (i + 1) := by
        simp [sourceOffset, activeAbs, rightAbs]
      simp only [foldedCellOfTapeAt]
      rw [hleft, hright]
      simp [foldedBlank, inputSymbol,
        TM0Route.partrecStartedTM0Input, TM0Route.partrecStartedTM2Input,
        Turing.TM2to1.trInit, Turing.PartrecToTM2.trList,
        Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk',
        Turing.Tape.nth]

theorem FoldedTapeRel_init_right_zero (tc : Turing.ToPartrec.Code) :
    FoldedTapeRel
      (Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input).Tape
      FoldSide.right 0
      (Function.update (fun _ => foldedBlank) 0
        (foldedOriginSymbol (inputSymbol 0))) := by
  intro i
  exact (foldedCellOfTapeAt_init_right_zero tc i).symm

theorem FoldedConfigRel_runEmpty_two (tc : Turing.ToPartrec.Code) :
    FoldedConfigRel tc
      (Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input)
      ((program tc).runEmpty 2) := by
  rw [program_runEmpty_two]
  refine ⟨FoldSide.right, ?_, ?_, ?_⟩
  · simpa [Turing.TM0.init] using default_mem_partrecStartedTM0LabelList tc
  · simp [foldedSimStartState, foldedSimStartStateCode, foldedSimStateCode,
      foldedSimStateOfCode, TM0Route.partrecStartedTM0Start,
      TM0FiniteCompiler.stateCode_default tc, Turing.TM0.init]
  · exact FoldedTapeRel_init_right_zero tc

theorem program_runEmpty_add_two (tc : Turing.ToPartrec.Code) (n : Nat) :
    (program tc).runEmpty (n + 2) =
      Nat.iterate (program tc).nextID n ((program tc).runEmpty 2) := by
  unfold PostProgram.runEmpty
  rw [Function.iterate_add_apply]

theorem program_haltsEmpty_of_tm0_eval_dom (tc : Turing.ToPartrec.Code) :
    (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
      TM0Route.partrecStartedTM0Input).Dom →
      (program tc).HaltsEmpty := by
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
  rcases FoldedConfigRel_reaches_halt
      (tc := tc) (cfg := initCfg) (cfg' := haltCfg)
      (id := (program tc).runEmpty 2)
      (FoldedConfigRel_runEmpty_two tc) hreach hhalt with
    ⟨n, hn⟩
  refine ⟨n + 2, ?_⟩
  rw [program_runEmpty_add_two]
  exact hn

theorem tm0_reaches_halt_of_folded_halts
    {tc : Turing.ToPartrec.Code}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∀ n : Nat,
      (Nat.iterate (program tc).nextID n id).state = none →
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
          have hrel₁ := FoldedConfigRel_step hrel hstep
          have hhalt₁ :
              (Nat.iterate (program tc).nextID n ((program tc).nextID id)).state =
                none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_folded_halts hrel₁ n hhalt₁ with
            ⟨cfg', hreach, hterminal⟩
          refine ⟨cfg', ?_, hterminal⟩
          exact Relation.ReflTransGen.head (by simpa using hstep) hreach

theorem tm0_eval_dom_of_program_haltsEmpty (tc : Turing.ToPartrec.Code) :
    (program tc).HaltsEmpty →
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  rintro ⟨k, hhalt⟩
  cases k with
  | zero =>
      simp [PostProgram.runEmpty_zero, PostProgram.initialID] at hhalt
  | succ k =>
      cases k with
      | zero =>
          rw [show 1 = 1 by rfl, program_runEmpty_one] at hhalt
          simp at hhalt
      | succ n =>
          have hhalt' : ((program tc).runEmpty (n + 2)).state = none := by
            rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
            exact hhalt
          have hhaltIter :
              (Nat.iterate (program tc).nextID n ((program tc).runEmpty 2)).state =
                none := by
            rw [program_runEmpty_add_two] at hhalt'
            exact hhalt'
          let step :=
            Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
          let initCfg :=
            Turing.TM0.init (Λ := SourceLabel tc) TM0Route.partrecStartedTM0Input
          rcases tm0_reaches_halt_of_folded_halts
              (tc := tc) (cfg := initCfg) (id := (program tc).runEmpty 2)
              (FoldedConfigRel_runEmpty_two tc) n hhaltIter with
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

theorem program_haltsEmpty_iff_tm0_eval_dom (tc : Turing.ToPartrec.Code) :
    (program tc).HaltsEmpty ↔
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc)
        TM0Route.partrecStartedTM0Input).Dom := by
  exact ⟨tm0_eval_dom_of_program_haltsEmpty tc,
    program_haltsEmpty_of_tm0_eval_dom tc⟩

theorem program_haltsEmpty_iff_partrec_eval_dom (tc : Turing.ToPartrec.Code) :
    (program tc).HaltsEmpty ↔
      (StateTransition.eval
        (Turing.TM2.step TM0Route.partrecTM2)
        (TM0Route.partrecInit tc)).Dom := by
  exact (program_haltsEmpty_iff_tm0_eval_dom tc).trans
    ((TM0Route.partrecStartedTM0_eval_dom_iff_tm2 tc).trans
      (TM0Route.partrecStartedTM2_eval_dom_iff_partrec tc))

end TM0FoldedCompiler

end LeanWang
