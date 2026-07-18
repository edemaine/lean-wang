/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlPlan
import LeanWang.Kari.Hooper.GlobalSourceSemantics

/-!
# State bounds along abstract counter traces

The compiled counter controller allocates its logical-state interval using
all source and target states named by the fixed global counter program.  This
module proves that every abstract counter transition stays in that finite
set, and hence that every state reachable from the canonical input remains
inside the controller's logical interval.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlAbstractTrace

open CounterMachine CounterProgram
open CounterControlPlan
open SourceProgram

noncomputable section

/-- A target named by a global-program rule belongs to the linker state set. -/
theorem target_mem_programStates {source target : State}
    {instruction : Instruction}
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (htarget : target ∈ instructionTargets instruction) :
    target ∈ programStates := by
  unfold programStates
  apply List.mem_flatMap.mpr
  exact ⟨(source, instruction), hrule, by
    simp only [ruleStates, List.mem_cons]
    exact Or.inr htarget⟩

/-- Every defined abstract counter step lands at a state named by the fixed
program, independently of where the step started. -/
theorem state_mem_programStates_of_step {cfg nextCfg : Cfg}
    (hstep : step GlobalSourceProgram.program cfg = some nextCfg) :
    nextCfg.state ∈ programStates := by
  cases hlookup : lookupInstruction GlobalSourceProgram.program cfg.state with
  | none => simp [step, hlookup] at hstep
  | some instruction =>
      have hrule : (cfg.state, instruction) ∈
          GlobalSourceProgram.program :=
        rule_mem_of_lookupInstruction_eq_some hlookup
      cases instruction with
      | increment register target =>
          rw [step, hlookup] at hstep
          cases Option.some.inj hstep
          exact target_mem_programStates hrule (by simp [instructionTargets])
      | decrement register ifZero ifPositive =>
          rw [step, hlookup] at hstep
          by_cases hzero : cfg.registers.get register = 0
          · simp only [hzero, if_pos] at hstep
            cases Option.some.inj hstep
            exact target_mem_programStates hrule
              (by simp [instructionTargets])
          · simp only [hzero, if_false] at hstep
            cases Option.some.inj hstep
            exact target_mem_programStates hrule
              (by simp [instructionTargets])

/-- Every defined abstract counter step lands below the allocated logical
span. -/
theorem state_lt_logicalSpan_of_step {cfg nextCfg : Cfg}
    (hstep : step GlobalSourceProgram.program cfg = some nextCfg) :
    nextCfg.state < logicalSpan :=
  state_lt_logicalSpan (state_mem_programStates_of_step hstep)

/-- State-set membership is invariant along every finite abstract trace. -/
theorem state_mem_programStates_of_reaches {start finish : Cfg}
    (hstart : start.state ∈ programStates)
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish) :
    finish.state ∈ programStates := by
  induction hreach with
  | refl => exact hstart
  | tail _ hstep _ =>
      exact state_mem_programStates_of_step (by simpa using hstep)

/-- The logical-span bound is invariant along every finite abstract trace.
This version needs only a bound on the initial state. -/
theorem state_lt_logicalSpan_of_reaches {start finish : Cfg}
    (hstart : start.state < logicalSpan)
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program) start finish) :
    finish.state < logicalSpan := by
  induction hreach with
  | refl => exact hstart
  | tail _ hstep _ =>
      exact state_lt_logicalSpan_of_step (by simpa using hstep)

/-! ## The canonical input state -/

private theorem default_source_transition_defined
    (head : SourceMachine.Alphabet) :
    ∃ result, SourceMachine.machine (default : SourceMachine.State) head =
      some result := by
  let result := Turing.TM1to0.trAux UniversalTM0Semantic.tm1 head
    (UniversalTM0Semantic.tm1 default) default
  have hambient : UniversalTM0Semantic.tm0
      (default : SourceMachine.AmbientState) head = some result := rfl
  rcases hresult : result with ⟨nextState, action⟩
  have hnext : nextState ∈ UniversalTM0Semantic.tm0Support := by
    apply UniversalTM0Semantic.tm0_supports.2
    · simpa [hresult] using hambient
    · exact UniversalTM0Semantic.tm0_supports.1
  refine ⟨(⟨nextState, hnext⟩, action), ?_⟩
  have hdefault : (default : SourceMachine.State).val =
        (default : SourceMachine.AmbientState) := rfl
  change (match UniversalTM0Semantic.tm0
      (default : SourceMachine.State).val head with
    | none => none
    | some (q', action) =>
        if hq' : q' ∈ UniversalTM0Semantic.tm0Support then
          some ((⟨q', hq'⟩ : SourceMachine.State), action)
        else none) =
          some ((⟨nextState, hnext⟩ : SourceMachine.State), action)
  rw [hdefault, hambient, hresult]
  simp [hnext]

/-- The code-dependent canonical counter state occurs as a source of the
fixed global program and therefore belongs to `programStates`. -/
theorem canonicalCounterCfg_state_mem_programStates (c : Nat.Partrec.Code) :
    (GlobalSourceSemantics.canonicalCounterCfg c).state ∈ programStates := by
  let head := (UniversalTM0Semantic.input c).headI
  let key : GlobalSourceProgram.SourceKey :=
    (SourceControl.encodeStateFin (default : SourceMachine.State),
      SourceControl.encodeSymbol head)
  rcases default_source_transition_defined head with ⟨result, hmachine⟩
  rcases result with ⟨nextState, action⟩
  have hmachineKey : SourceMachine.machine
      (SourceControl.decodeStateFin key.1)
      (SourceControl.decodeSymbol key.2) = some (nextState, action) := by
    simpa [key] using hmachine
  have hruleKey :
      (controlCode (default : SourceMachine.State) head,
        .decrement .temp (GlobalSourceProgram.actionOffset key)
          (GlobalSourceProgram.actionOffset key)) ∈
        GlobalSourceProgram.keyProgram key := by
    simp [GlobalSourceProgram.keyProgram, key, hmachine]
  have hrule := GlobalSourceProgram.keyProgram_subset_program key _ hruleKey
  rw [GlobalSourceSemantics.canonicalCounterCfg_state]
  exact source_mem_programStates _ hrule

/-- The canonical abstract input starts inside the compiled controller's
logical-state interval. -/
theorem canonicalCounterCfg_state_lt_logicalSpan (c : Nat.Partrec.Code) :
    (GlobalSourceSemantics.canonicalCounterCfg c).state < logicalSpan :=
  state_lt_logicalSpan (canonicalCounterCfg_state_mem_programStates c)

/-- Every endpoint reachable from the canonical abstract input stays inside
the compiled controller's logical-state interval. -/
theorem reachable_from_canonical_state_lt_logicalSpan (c : Nat.Partrec.Code)
    {finish : Cfg}
    (hreach : StateTransition.Reaches
      (step GlobalSourceProgram.program)
      (GlobalSourceSemantics.canonicalCounterCfg c) finish) :
    finish.state < logicalSpan :=
  state_lt_logicalSpan_of_reaches
    (canonicalCounterCfg_state_lt_logicalSpan c) hreach

end

end CounterControlAbstractTrace
end Hooper
end Kari
end LeanWang
