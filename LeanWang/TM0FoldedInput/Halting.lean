/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.TM0FoldedInput.Reach

/-!
Halting equivalence for a parameterized initializer followed by the fixed
position-coded folded simulation.
-/

noncomputable section

namespace LeanWang

namespace TM0FoldedCompiler

def PostHaltsFrom (P : PostProgram) (id : PostID) : Prop :=
  ∃ n : Nat, (Nat.iterate P.nextID n id).state = none

theorem iterate_nextID_eq_of_halt
    (P : PostProgram) {id : PostID} (hhalt : id.state = none) (n : Nat) :
    Nat.iterate P.nextID n id = id := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, PostProgram.nextID_of_halt P id hhalt, ih]

theorem postHaltsFrom_iff_of_reaches_running
    {P : PostProgram} {a b : PostID}
    (hab : PostReaches P a b) (hb : b.state ≠ none) :
    PostHaltsFrom P a ↔ PostHaltsFrom P b := by
  rcases hab with ⟨m, hm⟩
  constructor
  · rintro ⟨n, hn⟩
    by_cases hmn : m ≤ n
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨k, ?_⟩
      have hn' :
          (Nat.iterate P.nextID (k + m) a).state = none := by
        simpa [Nat.add_comm] using hn
      rw [Function.iterate_add_apply, hm] at hn'
      exact hn'
    · have hnm : n ≤ m := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exfalso
      apply hb
      rw [← hm, Nat.add_comm, Function.iterate_add_apply]
      rw [iterate_nextID_eq_of_halt P hn]
      exact hn
  · rintro ⟨n, hn⟩
    refine ⟨n + m, ?_⟩
    rw [Function.iterate_add_apply, hm]
    exact hn

theorem inputProgram_haltsFrom_sim_of_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ [])
    (hdomEval :
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc) input).Dom) :
    PostHaltsFrom (positionProgramDataOnInput tc input)
      (simInitID input (input.length - 1)) := by
  let step :=
    Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
  let initCfg :=
    Turing.TM0.init (Λ := SourceLabel tc) input
  have hdomState : (StateTransition.eval step initCfg).Dom := by
    dsimp [step, initCfg] at *
    rw [Turing.TM0.eval] at hdomEval
    exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
      (StateTransition.eval
        (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
        (Turing.TM0.init (Λ := SourceLabel tc) input))).1 hdomEval
  let haltCfg := (StateTransition.eval step initCfg).get hdomState
  have hmem : haltCfg ∈ StateTransition.eval step initCfg :=
    Part.get_mem hdomState
  rcases StateTransition.mem_eval.1 hmem with ⟨hreach, hhalt⟩
  exact FoldedConfigRel_input_reaches_halt
    (tc := tc) (input := input) (cfg := initCfg) (cfg' := haltCfg)
    (id := simInitID input (input.length - 1))
    (FoldedConfigRel_simInitID tc hinput) hreach hhalt

theorem tm0_reaches_halt_of_inputProgram_halts
    {tc : Turing.ToPartrec.Code} {input : List SourceSymbol}
    {cfg : Turing.TM0.Cfg SourceSymbol (SourceLabel tc)} {id : PostID}
    (hrel : FoldedConfigRel tc cfg id) :
    ∀ n : Nat,
      (Nat.iterate (positionProgramDataOnInput tc input).nextID n id).state = none →
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
          have hrel₁ := FoldedConfigRel_input_step
            (input := input) hrel hstep
          have hhalt₁ :
              (Nat.iterate (positionProgramDataOnInput tc input).nextID n
                  ((positionProgramDataOnInput tc input).nextID id)).state = none := by
            simpa [Function.iterate_succ_apply] using hhalt
          rcases tm0_reaches_halt_of_inputProgram_halts hrel₁ n hhalt₁ with
            ⟨cfg', hreach, hterminal⟩
          refine ⟨cfg', ?_, hterminal⟩
          exact Relation.ReflTransGen.head (by simpa using hstep) hreach

theorem tm0_eval_dom_of_inputProgram_haltsFrom_sim
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ [])
    (hhalts : PostHaltsFrom (positionProgramDataOnInput tc input)
      (simInitID input (input.length - 1))) :
    (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc) input).Dom := by
  rcases hhalts with ⟨n, hhalt⟩
  let step := Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc)
  let initCfg := Turing.TM0.init (Λ := SourceLabel tc) input
  rcases tm0_reaches_halt_of_inputProgram_halts
      (tc := tc) (input := input) (cfg := initCfg)
      (id := simInitID input (input.length - 1))
      (FoldedConfigRel_simInitID tc hinput) n hhalt with
    ⟨cfg', hreach, hterminal⟩
  have hmem : cfg' ∈ StateTransition.eval step initCfg := by
    exact StateTransition.mem_eval.2 ⟨hreach, hterminal⟩
  have hdomState : (StateTransition.eval step initCfg).Dom :=
    Part.dom_iff_mem.2 ⟨cfg', hmem⟩
  rw [Turing.TM0.eval]
  exact (TM0Route.part_dom_map_iff (fun c => c.Tape.right₀)
    (StateTransition.eval
      (Turing.TM0.step (TM0Route.partrecStartedTM0Machine tc))
      (Turing.TM0.init (Λ := SourceLabel tc) input))).2 hdomState

theorem positionProgramDataOnInput_haltsEmpty_iff_tm0_eval_dom
    (tc : Turing.ToPartrec.Code) {input : List SourceSymbol}
    (hinput : input ≠ []) :
    (positionProgramDataOnInput tc input).HaltsEmpty ↔
      (Turing.TM0.eval (TM0Route.partrecStartedTM0Machine tc) input).Dom := by
  let P := positionProgramDataOnInput tc input
  let sim := simInitID input (input.length - 1)
  have hreach : PostReaches P P.initialID sim :=
    initialID_reaches_simInitID tc hinput
  have hsim : sim.state ≠ none := by
    simp [sim, simInitID]
  have hprefix : P.HaltsEmpty ↔ PostHaltsFrom P sim := by
    exact postHaltsFrom_iff_of_reaches_running hreach hsim
  rw [hprefix]
  exact ⟨tm0_eval_dom_of_inputProgram_haltsFrom_sim tc hinput,
    inputProgram_haltsFrom_sim_of_tm0_eval_dom tc hinput⟩

end TM0FoldedCompiler

end LeanWang
