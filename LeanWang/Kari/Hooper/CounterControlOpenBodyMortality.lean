/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlOpenInstructionResolution
import LeanWang.Kari.Hooper.CounterControlOpenMortality
import LeanWang.Kari.Hooper.CounterControlPrefixInstructionResolution

/-!
# Mortality of instruction bodies on open counter cores

Validation converse can first reconstruct the five-boundary core exactly at
the selected instruction body.  Before choosing a finite first obstruction,
one must exclude an infinite blank ray.  The existing open-core mortality
theorem starts at logical control; this module supplies the short missing
bridge from the already-validated body to the next logical configuration.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlOpenBodyMortality

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlBridge
open CounterControlCoreFrame CounterControlTagFreeOpen
open CounterControlOpenInstructionResolution
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Under source mortality, an exact post-validation instruction body on an
open tag-free core cannot be immortal. -/
theorem haltsFrom_body_of_coreOpen
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat) (instruction : Instruction)
    (registers : Registers) (T : FullTM0.Tape (Symbol numTags))
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hopen : CoreOpenRepresents registers growth T) :
    FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
      (bodyCfg base c growth ⟨source, registers⟩ instruction T) := by
  cases instruction with
  | increment register next =>
      have hcommands : ∀ raw,
          raw ∈ incrementShiftCommands growth source register →
            raw ∈ rawCommands := by
        intro raw hraw
        apply CounterControlPlan.command_mem_rawCommands_of_rule
          growth hrule
        simp [commandsForRule, incrementCommands, hraw]
      have hschedule := machine_reaches_incrementSchedule_or_halts_of_open
        base c source register hopen hcommands
      have hhandoff := machine_reaches_incrementHandoff_of_open base c source
        next register hrule hopen
      have hnext := incrementCoreTape_preserves_open hopen register
      have hrecovery := machine_reaches_incrementRecovery_or_halts_of_core
        base c source next register hrule hnext.toCoreRepresents
      have hrun := FullTM0.ResolvesTo.trans
        (hschedule.imp (fun hsuccess => hsuccess.1) id)
        (FullTM0.ResolvesTo.trans (Or.inl hhandoff) hrecovery)
      rcases hrun with hreach | hhalts
      · apply FullTM0.HaltsFrom.of_reaches (by
          simpa [bodyCfg, bodyEntry, searchRef,
            CounterControlPlan.resolve] using hreach)
        simpa [layoutEnd_increment] using
          (CounterControlOpenMortality.haltsFrom_logical_of_coreOpen
            base c hmortal growth ⟨next, registers.increment register⟩
            (incrementCoreTape registers growth register T)
            (state_lt_logicalSpan
              (CounterControlAbstractTrace.target_mem_programStates hrule
                (by simp [instructionTargets]))) hnext)
      · simpa [bodyCfg, bodyEntry, searchRef,
          CounterControlPlan.resolve] using hhalts
  | decrement register ifZero ifPositive =>
      have hroute := machine_reaches_decrementToTest_or_halts_of_core base c
        growth source ifZero ifPositive register hrule
        hopen.toCoreRepresents
      have htest :=
        CounterControlInstructionSemantics.machine_reaches_decrementTest
          base c source ifZero ifPositive register hrule
          (spec := openSpec registers growth) T (by
            change (atLogical growth T
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register))).read = _
            rw [atLogical_read]
            exact hopen.boundary _)
      have htest' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨resolve base c (directRef growth source testDirectSlot),
            atLogical growth T
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register))⟩
          ⟨resolve base c (directRef growth source branchDirectSlot),
            atLogical growth T
              (boundaryOffset registers
                (MarkerSchedule.decrementStartBoundary register) - 1)⟩ := by
        simpa [openSpec] using htest
      by_cases hzero : registers.get register = 0
      · have hzeroRoute :=
          machine_reaches_decrementZeroRecovery_or_halts_of_core
            base c growth source ifZero ifPositive register hrule
            hopen.toCoreRepresents hzero
        have hrun := FullTM0.ResolvesTo.trans hroute
          (FullTM0.ResolvesTo.trans (Or.inl htest') hzeroRoute)
        rcases hrun with hreach | hhalts
        · apply FullTM0.HaltsFrom.of_reaches (by
            simpa [bodyCfg] using hreach)
          exact CounterControlOpenMortality.haltsFrom_logical_of_coreOpen
            base c hmortal growth ⟨ifZero, registers⟩ T
            (state_lt_logicalSpan
              (CounterControlAbstractTrace.target_mem_programStates hrule
                (by simp [instructionTargets]))) hopen
        · simpa [bodyCfg] using hhalts
      · have hpositive : 0 < registers.get register :=
          Nat.pos_of_ne_zero hzero
        have hhandoff := machine_reaches_decrementPositiveHandoff_of_core
          base c source ifZero ifPositive register hrule
          hopen.toCoreRepresents hpositive
        have hcommands : ∀ raw,
            raw ∈ decrementShiftCommands growth source register →
              raw ∈ rawCommands := by
          intro raw hraw
          apply CounterControlPlan.command_mem_rawCommands_of_rule
            growth hrule
          simp [commandsForRule, decrementCommands, hraw]
        have hschedule := machine_reaches_decrementSchedule_or_halts_of_open
          base c source register hopen hpositive hcommands
        have hfinish := machine_reaches_decrementPositiveFinish_of_core
          base c source ifZero ifPositive register hrule growth T hpositive
        have hscheduleFinish :
            FullTM0.Reaches (CounterControlNestingBridge.machine base c)
                ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
                  atLogical growth T
                    (boundaryOffset registers
                      (MarkerSchedule.decrementStartBoundary register))⟩
                ⟨logicalState base c growth ifPositive,
                  atLogical growth
                    (decrementCoreTape registers growth register T)
                    (layoutEnd (registers.decrement register))⟩ ∨
              FullTM0.HaltsFrom (CounterControlNestingBridge.machine base c)
                ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
                  atLogical growth T
                    (boundaryOffset registers
                      (MarkerSchedule.decrementStartBoundary register))⟩ := by
          rcases hschedule with hschedule | hhalts
          · exact Or.inl (hschedule.1.trans hfinish)
          · exact Or.inr hhalts
        have hrun := FullTM0.ResolvesTo.trans hroute
          (FullTM0.ResolvesTo.trans (Or.inl htest')
            (FullTM0.ResolvesTo.trans (Or.inl hhandoff)
              hscheduleFinish))
        rcases hrun with hreach | hhalts
        · have hnext := decrementCoreTape_preserves_open hopen register
            hpositive
          apply FullTM0.HaltsFrom.of_reaches (by
              simpa [bodyCfg] using hreach)
          exact CounterControlOpenMortality.haltsFrom_logical_of_coreOpen
            base c hmortal growth
            ⟨ifPositive, registers.decrement register⟩
            (decrementCoreTape registers growth register T)
            (state_lt_logicalSpan
              (CounterControlAbstractTrace.target_mem_programStates hrule
                (by simp [instructionTargets]))) hnext
        · simpa [bodyCfg] using hhalts

end

end CounterControlOpenBodyMortality
end Hooper
end Kari
end LeanWang
