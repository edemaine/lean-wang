/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrement
import LeanWang.Kari.Hooper.CounterControlDecrementShiftContinuation
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding

/-!
# Final outward validation followed by a clock decrement

The clock is the one decrement register whose route to the test is empty.
Consequently the final outward validation command reaches the test directly
on boundary `4`.  After the test and its forced two-way branch, the original
outward gap can be retagged as either the first positive shift or the first
zero-recovery search.  This retains the caller's distance comparison while
the existing total continuations discharge the remainder of the branch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardDecrementClock

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGenuineValidation
open CounterControlGenuineValidationOutward

noncomputable section

set_option maxRecDepth 10000

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Retag a retained boundary-`4` gap with another generated command having
the same target and physical search direction. -/
private def retagFour
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (htarget : (CounterControlCommandAt.compileRawCommand base c raw hraw).target =
      Target.boundary (4 : Fin 5))
    (hdirection :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection =
        orient growth .right)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches current.outer
      (orient growth .right) current.distance) : GenuineSearch base c := by
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  exact {
    search := search
    outer := current.outer
    distance := current.distance
    gap := by
      have hcommand : command base c search =
          CounterControlCommandAt.compileRawCommand base c raw hraw := by
        rfl
      rw [hcommand, htarget, hdirection]
      exact hgap }

@[simp] private theorem retagFour_distance
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c) (growth : Turing.Dir)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) htarget hdirection hgap :
    (retagFour base c current growth raw hraw htarget hdirection hgap).distance =
      current.distance :=
  rfl

@[simp] private theorem retagFour_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c) (growth : Turing.Dir)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) htarget hdirection hgap :
    (retagFour base c current growth raw hraw htarget hdirection hgap).selectedRaw =
      raw := by
  exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw

private theorem retagFour_foundTape
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c) (growth : Turing.Dir)
    (raw : RawCommand) (hraw : raw ∈ rawCommands) htarget hdirection hgap
    (hcurrentDirection : current.direction = orient growth .right) :
    (retagFour base c current growth raw hraw htarget hdirection hgap).foundTape =
      current.foundTape := by
  change current.outer.moveN
      (command base c (CounterControlCommandAt.rawTag raw hraw)).searchDirection
      current.distance =
    current.outer.moveN current.direction current.distance
  have hcommand : command base c (CounterControlCommandAt.rawTag raw hraw) =
      CounterControlCommandAt.compileRawCommand base c raw hraw := by
    rfl
  rw [hcommand, hdirection, hcurrentDirection]

/-- At the branch direct state, immortality forces one of the two rules
owned by the clock-decrement instruction to match. -/
private theorem clockBranchRead_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source ifZero ifPositive : Nat}
    (hprogram : (source, .decrement .clock ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source branchDirectSlot), T⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    T.read = blankSymbol ∨ T.read = boundarySymbol 3 := by
  simpa [AnchoredCounterGeometry.registerGap] using
    (CounterControlDecrementEntry.branchRead_of_reaches base c hprogram
      (foundCfg current) T hreaches himmortal)

private def outwardHandoff_of_monotone
    {base : Nat} {c : Nat.Partrec.Code}
    {current next : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat}
    {instruction : CounterMachine.Instruction}
    {progress : ValidationEnd current growth source instruction}
    {hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source instruction) .preserve}
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) (foundCfg next))
    (hdistance : current.distance ≤ next.distance)
    (outcome : FoundMonotoneGuardedEntryOutcome next) :
    OutwardInstructionHandoff current (OutwardObligation.four progress hraw) := by
  cases outcome with
  | logical core htail hinside =>
      exact .logical core (hreaches.trans htail) (hdistance.trans hinside)
  | nextSearch guarded htail hle =>
      exact .nextSearch guarded (hreaches.trans htail) (hdistance.trans hle)

/-- The final outward validation command followed by a clock decrement has
a monotone handoff through either the positive shift or zero recovery. -/
theorem outwardFour_clockDecrement_handoff
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source ifZero ifPositive : Nat)
    (hrule : (source, .decrement .clock ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : ValidationEnd current growth source
      (.decrement .clock ifZero ifPositive))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source
          (.decrement .clock ifZero ifPositive)) .preserve)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current
      (OutwardObligation.four progress hraw)) := by
  have hread : current.foundTape.read = boundarySymbol 4 :=
    outwardFour_foundTape_read current growth source
      (.decrement .clock ifZero ifPositive) hraw
  let testRule : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot, .boundary 4,
      directRef growth source branchDirectSlot, .left⟩
  have htestRule : testRule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change testRule ∈ validationRules growth source ++
      decrementRules growth source .clock ifZero ifPositive
    apply List.mem_append_right
    simp [testRule, decrementRules,
      MarkerSchedule.decrementStartBoundary]
  have htestMatch : testRule.read.Matches current.foundTape.read := by
    simpa [testRule, RawRead.Matches] using hread
  have htestLocal := CounterControlDirectSemantics.reaches_directRule
    base c testRule htestRule current.foundTape htestMatch
  have htest : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        current.foundTape⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        current.foundTape.move (orient growth .left)⟩ := by
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [testRule] using htestLocal
  have hbody := outwardFour_reaches_bodyEntry progress hraw
  have hbodyTest : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source testDirectSlot),
        current.foundTape⟩ := by
    simpa [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
      using hbody
  have hbranch : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source branchDirectSlot),
        current.foundTape.move (orient growth .left)⟩ :=
    hbodyTest.trans htest
  have hbranchRead := clockBranchRead_of_immortal base c hrule
    (current.foundTape.move (orient growth .left)) hbranch himmortal
  have hgap := outwardFour_gap current growth source
    (.decrement .clock ifZero ifPositive) hraw
  have hcurrentDirection := outwardFour_direction current growth source
    (.decrement .clock ifZero ifPositive) hraw
  have hback :
      (current.foundTape.move (orient growth .left)).move
          (orient growth .right) = current.foundTape := by
    cases growth <;> simp [orient, FullTM0.Tape.move]
  rcases CounterControlDecrementEntry.branchStep_of_read base c hrule
      (current.foundTape.move (orient growth .left)) hbranchRead with ⟨step⟩
  rcases step with ⟨hblank, hpositiveStepRaw⟩ |
    ⟨hboundary, hzeroStepRaw⟩
  ·
    have hpositiveStep : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          current.foundTape.move (orient growth .left)⟩
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          current.foundTape⟩ := by
      rw [hback] at hpositiveStepRaw
      exact hpositiveStepRaw
    have hpositiveEntry := hbranch.trans hpositiveStep
    let raw := CounterControlGenuineDecrementEntry.firstDecrementShiftRaw
      growth source .clock
    have hrawMem : raw ∈ rawCommands :=
      CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_mem_rawCommands
        growth source .clock ifZero ifPositive hrule
    have htarget :
        (CounterControlCommandAt.compileRawCommand base c raw hrawMem).target =
          Target.boundary (4 : Fin 5) := by
      simpa [raw, MarkerSchedule.decrementStartBoundary] using
        CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_target
          base c growth source .clock hrawMem
    have hdirection :
        (CounterControlCommandAt.compileRawCommand base c raw
          hrawMem).searchDirection = orient growth .right :=
      CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_direction
        base c growth source .clock hrawMem
    let next := retagFour base c current growth raw hrawMem htarget
      hdirection hgap
    have htargetMatch :
        (CounterControlCommandAt.compileRawCommand base c raw hrawMem).target.Matches
          current.foundTape.read := by
      rw [htarget]
      simpa [Target.Matches] using hread
    let immediate := CounterControlGenuineDecrementEntry.immediateSearch
      base c raw hrawMem current.foundTape htargetMatch
    have hentry : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        immediate.cfg := by
      rw [CounterControlGenuineDecrementEntry.immediateSearch_cfg]
      change FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          current.foundTape⟩
      exact hpositiveEntry
    have himmortalImmediate := FullTM0.ImmortalFrom.of_reaches himmortal hentry
    have hfoundImmediate := reaches_foundCfg_of_immortal immediate
      himmortalImmediate
    have hfoundTapeNext : next.foundTape = current.foundTape :=
      retagFour_foundTape base c current growth raw hrawMem htarget
        hdirection hgap hcurrentDirection
    have himmediateSelected : immediate.selectedRaw = raw := by
      exact CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
        base c raw hrawMem current.foundTape htargetMatch
    have hnextSelected : next.selectedRaw = raw := by
      exact retagFour_selectedRaw base c current growth raw hrawMem htarget
        hdirection hgap
    have himmediateFoundTape : immediate.foundTape = current.foundTape := by
      change current.foundTape.moveN immediate.direction 0 = current.foundTape
      simp
    have hfoundEq : foundCfg immediate = foundCfg next := by
      rw [immediate.foundCfg_eq, next.foundCfg_eq]
      rw [himmediateSelected, hnextSelected, himmediateFoundTape,
        hfoundTapeNext]
    have hreachesNext : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        (foundCfg next) := by
      rw [← hfoundEq]
      exact hentry.trans hfoundImmediate
    have himmortalNext := FullTM0.ImmortalFrom.of_reaches himmortal
      hreachesNext
    have hcommand : next.selectedRaw ∈
        decrementShiftCommands growth source .clock := by
      rw [retagFour_selectedRaw]
      exact CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_mem
        growth source .clock
    rcases
        CounterControlDecrementShiftContinuation.foundMonotoneGuardedEntryOutcome_of_decrementShift
          base c hmortal next growth source .clock ifZero ifPositive hrule
          hcommand himmortalNext with ⟨outcome⟩
    exact ⟨outwardHandoff_of_monotone hreachesNext (by simp [next])
      outcome⟩
  ·
    have hzeroStep : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          current.foundTape.move (orient growth .left)⟩
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          current.foundTape⟩ := by
      rw [hback] at hzeroStepRaw
      exact hzeroStepRaw
    have hzeroEntry := hbranch.trans hzeroStep
    let raw := CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw
      growth source .clock ifZero
    have hrawMem : raw ∈ rawCommands :=
      CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_mem_rawCommands
        growth source .clock ifZero ifPositive hrule
    have htarget :
        (CounterControlCommandAt.compileRawCommand base c raw hrawMem).target =
          Target.boundary (4 : Fin 5) := by
      simpa [raw, MarkerSchedule.decrementStartBoundary] using
        CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_target
          base c growth source .clock ifZero hrawMem
    have hdirection :
        (CounterControlCommandAt.compileRawCommand base c raw
          hrawMem).searchDirection = orient growth .right :=
      CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_direction
        base c growth source .clock ifZero hrawMem
    let next := retagFour base c current growth raw hrawMem htarget
      hdirection hgap
    have htargetMatch :
        (CounterControlCommandAt.compileRawCommand base c raw hrawMem).target.Matches
          current.foundTape.read := by
      rw [htarget]
      simpa [Target.Matches] using hread
    let immediate := CounterControlGenuineDecrementEntry.immediateSearch
      base c raw hrawMem current.foundTape htargetMatch
    have hentry : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        immediate.cfg := by
      rw [CounterControlGenuineDecrementEntry.immediateSearch_cfg]
      change FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          current.foundTape⟩
      exact hzeroEntry
    have himmortalImmediate := FullTM0.ImmortalFrom.of_reaches himmortal hentry
    have hfoundImmediate := reaches_foundCfg_of_immortal immediate
      himmortalImmediate
    have hfoundTapeNext : next.foundTape = current.foundTape :=
      retagFour_foundTape base c current growth raw hrawMem htarget
        hdirection hgap hcurrentDirection
    have himmediateSelected : immediate.selectedRaw = raw := by
      exact CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
        base c raw hrawMem current.foundTape htargetMatch
    have hnextSelected : next.selectedRaw = raw := by
      exact retagFour_selectedRaw base c current growth raw hrawMem htarget
        hdirection hgap
    have himmediateFoundTape : immediate.foundTape = current.foundTape := by
      change current.foundTape.moveN immediate.direction 0 = current.foundTape
      simp
    have hfoundEq : foundCfg immediate = foundCfg next := by
      rw [immediate.foundCfg_eq, next.foundCfg_eq]
      rw [himmediateSelected, hnextSelected, himmediateFoundTape,
        hfoundTapeNext]
    have hreachesNext : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        (foundCfg next) := by
      rw [← hfoundEq]
      exact hentry.trans hfoundImmediate
    have himmortalNext := FullTM0.ImmortalFrom.of_reaches himmortal
      hreachesNext
    have hcommand : next.selectedRaw ∈
        routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero .clock) := by
      rw [retagFour_selectedRaw]
      exact CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_mem
        growth source .clock ifZero
    rcases CounterControlGenuineRouteEmbedding.zeroRecovery_logical_of_rule
        base c hmortal next himmortalNext growth source .clock ifZero
        ifPositive hrule hcommand with ⟨outcome⟩
    exact ⟨outwardHandoff_of_monotone hreachesNext (by simp [next])
      outcome⟩

end

end CounterControlGenuineValidationOutwardDecrementClock
end Hooper
end Kari
end LeanWang
