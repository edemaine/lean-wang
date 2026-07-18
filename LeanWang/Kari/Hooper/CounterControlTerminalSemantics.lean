/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDeterministic
import LeanWang.Kari.Hooper.CounterControlNestingBridge

/-!
# Terminal semantics of compiled logical counter states

The counter controller allocates two oriented copies of every logical state.
This file proves that a logical state with no source instruction in the fixed
counter program is also terminal in the compiled `TM0` table.  The explicit
`state < logicalSpan` hypothesis is essential: outside the allocated logical
interval, the numeric expression for a logical state can alias a later direct
state interval.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlTerminalSemantics

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlDeterministic

noncomputable section

/-- A bounded logical state whose counter-program lookup fails is absent from
the direct-rule source states. -/
theorem logicalState_not_mem_directTable
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (state : Nat) (hstate : state < logicalSpan)
    (hlookup : lookupInstruction GlobalSourceProgram.program state = none) :
    logicalState base c growth state ∉
      FiniteTM0.sourceStates (directTable base c) := by
  intro hsource
  rcases List.mem_map.mp hsource with ⟨rule, hrule, hsourceEq⟩
  have htableKey : rule.1 ∈ (directTable base c).map Prod.fst :=
    List.mem_map.mpr ⟨rule, hrule, rfl⟩
  rw [directTable_keys] at htableKey
  rcases List.mem_map.mp htableKey with
    ⟨numericKey, hnumericKey, htranslated⟩
  rw [rawDirectKeys_eq] at hnumericKey
  rcases List.mem_map.mp hnumericKey with
    ⟨controlKey, hcontrolKey, hnumericEq⟩
  have hresolved :
      rightLogicalBase base c + sourceOffset controlKey.1 =
        logicalState base c growth state := by
    have hnumericSource : sourceOffset controlKey.1 = numericKey.1 := by
      simpa using congrArg Prod.fst hnumericEq
    calc
      rightLogicalBase base c + sourceOffset controlKey.1 =
          rightLogicalBase base c + numericKey.1 := by
        rw [hnumericSource]
      _ = rule.1.1 := congrArg Prod.fst htranslated
      _ = logicalState base c growth state := hsourceEq
  have hlogicalResolved :
      logicalState base c growth state =
        rightLogicalBase base c +
          sourceOffset (.logical growth state) := by
    simpa [resolve] using
      (resolve_eq_add_sourceOffset base c
        (reference := ControlRef.logical growth state) (by simp [IsCounterSource]))
  have hoffset : sourceOffset controlKey.1 =
      sourceOffset (.logical growth state) := by
    exact Nat.add_left_cancel (hresolved.trans hlogicalResolved)
  have hreference : controlKey.1 = .logical growth state :=
    sourceOffset_injective_on
      (rawDirectControlKeys_wellFormed hcontrolKey)
      (by simpa [WellFormedSource] using hstate)
      hoffset
  have hprogramSource :
      ∃ instruction, (state, instruction) ∈ GlobalSourceProgram.program := by
    simp only [rawDirectControlKeys, List.mem_append,
      rawDirectControlKeysFor, List.mem_flatMap] at hcontrolKey
    rcases hcontrolKey with
      ⟨programRule, hprogram, hlocal⟩ |
      ⟨programRule, hprogram, hlocal⟩
    · have howns := rawDirectControlKeysForRule_owns .right
        programRule controlKey hlocal
      rcases programRule with ⟨source, instruction⟩
      rw [hreference] at howns
      change growth = .right ∧ state = source at howns
      exact ⟨instruction, by simpa [← howns.2] using hprogram⟩
    · have howns := rawDirectControlKeysForRule_owns .left
        programRule controlKey hlocal
      rcases programRule with ⟨source, instruction⟩
      rw [hreference] at howns
      change growth = .left ∧ state = source at howns
      exact ⟨instruction, by simpa [← howns.2] using hprogram⟩
  rcases hprogramSource with ⟨instruction, hprogram⟩
  have hsome : lookupInstruction GlobalSourceProgram.program state =
      some instruction :=
    (CounterProgram.lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hprogram
  rw [hlookup] at hsome
  simp at hsome

/-- Every allocated logical state lies at or after the first state following
the shared canonical initializer. -/
private theorem initializerEnd_le_logicalState
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (state : Nat) :
    initializerEnd base c ≤ logicalState base c growth state := by
  cases growth with
  | left =>
      simp [initializerEnd, logicalState, logicalBase, leftLogicalBase,
        rightDirectBase, rightLogicalBase]
      omega
  | right =>
      simp [initializerEnd, logicalState, logicalBase, rightLogicalBase]

/-- A bounded logical state with no source instruction is absent from the
entire compiled controller table, including the bounded-search controller and
the shared initializer. -/
theorem logicalState_not_mem_table
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (state : Nat) (hstate : state < logicalSpan)
    (hlookup : lookupInstruction GlobalSourceProgram.program state = none) :
    logicalState base c growth state ∉
      FiniteTM0.sourceStates (CounterControlPlan.table base c) := by
  intro hsource
  simp only [CounterControlPlan.table, BoundedMarkerProgram.table, coreTable,
    FiniteTM0.sourceStates, List.map_append, List.mem_append] at hsource
  have hlower := initializerEnd_le_logicalState base c growth state
  rcases hsource with hcontroller | hinitializer | hdirect
  · have hcontrollerUpper :=
      BoundedMarkerProgram.source_mem_controllerTable hcontroller
    rw [controllerCoreEntry_eq base c] at hcontrollerUpper
    have hentryUpper :
        controllerCoreEntry base c < initializerEnd base c := by
      simp only [initializerEnd, CanonicalInitializerProgram.exitState]
      omega
    exact (Nat.not_lt_of_ge hlower)
      (hcontrollerUpper.trans hentryUpper)
  · have hinitializerUpper :=
      (CanonicalInitializerProgram.source_mem_table hinitializer).2
    exact (Nat.not_lt_of_ge hlower) hinitializerUpper
  · exact logicalState_not_mem_directTable base c growth state hstate
      hlookup hdirect

/-- At a bounded logical state corresponding to a halted counter
configuration, the compiled finite machine has no transition on any scanned
symbol. -/
theorem machine_eq_none_of_counter_step_none
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (cfg : CounterMachine.Cfg) (hstate : cfg.state < logicalSpan)
    (hhalt : CounterMachine.step GlobalSourceProgram.program cfg = none)
    (symbol : Symbol numTags) :
    CounterControlNestingBridge.machine base c
        (logicalState base c growth cfg.state) symbol = none := by
  have hlookup :=
    (CounterMachine.step_eq_none_iff GlobalSourceProgram.program cfg).1 hhalt
  simpa [CounterControlNestingBridge.machine, BoundedMarkerProgram.machine,
    CounterControlPlan.table]
    using FiniteTM0.machine_eq_none_of_state_not_mem
      (logicalState_not_mem_table base c growth cfg.state hstate hlookup)
      symbol

/-- A concrete compiled controller halts immediately at the exact logical
configuration representing a halted bounded counter configuration. -/
theorem machine_step_eq_none_of_counter_step_none
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (cfg : CounterMachine.Cfg) (T : FullTM0.Tape (Symbol numTags))
    (hstate : cfg.state < logicalSpan)
    (hhalt : CounterMachine.step GlobalSourceProgram.program cfg = none) :
    FullTM0.step (CounterControlNestingBridge.machine base c)
      ⟨logicalState base c growth cfg.state, T⟩ = none := by
  unfold FullTM0.step
  rw [machine_eq_none_of_counter_step_none base c growth cfg hstate hhalt
    T.read]
  rfl

end

end CounterControlTerminalSemantics
end Hooper
end Kari
end LeanWang
