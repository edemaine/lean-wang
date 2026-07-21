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

/-! ## Retagging the forced clock branch -/

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

/-- A generated clock-decrement branch retagged onto the original outward
gap, together with the operational facts needed by either branch
continuation. -/
private structure RetaggedBranch
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c) (raw : RawCommand) where
  next : GenuineSearch base c
  selectedRaw : next.selectedRaw = raw
  reaches : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current) (foundCfg next)
  immortal : FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c) (foundCfg next)
  distance_eq : next.distance = current.distance

/-- Turn an exact generated branch entry into a genuine search carrying the
original outward gap.  Immortality supplies the generated search's found
state; retagging identifies it with the requested branch command. -/
private def retaggedBranch
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c) (growth : Turing.Dir) (target : Fin 5)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (htarget :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target =
        Target.boundary target)
    (hdirection :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection =
        orient growth .right)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches current.outer
      (orient growth .right) current.distance)
    (hcurrentDirection : current.direction = orient growth .right)
    (hread : current.foundTape.read = boundarySymbol target)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (hsearchEntry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c raw.address, current.foundTape⟩) :
    RetaggedBranch base c current raw := by
  have htargetMatch :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
        current.foundTape.read := by
    rw [htarget]
    simpa [Target.Matches] using hread
  let immediate := CounterControlGenuineDecrementEntry.immediateSearch
    base c raw hraw current.foundTape htargetMatch
  let next := GenuineSearch.retagBoundary base c current growth target raw
    hraw htarget hdirection hgap
  have hentry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      immediate.cfg := by
    rw [CounterControlGenuineDecrementEntry.immediateSearch_cfg]
    exact hsearchEntry
  have himmortalImmediate := FullTM0.ImmortalFrom.of_reaches himmortal hentry
  have hfoundImmediate := reaches_foundCfg_of_immortal immediate
    himmortalImmediate
  have hfoundTapeNext : next.foundTape = current.foundTape :=
    GenuineSearch.retagBoundary_foundTape base c current growth target raw
      hraw htarget hdirection hgap hcurrentDirection
  have himmediateSelected : immediate.selectedRaw = raw :=
    CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
      base c raw hraw current.foundTape htargetMatch
  have hnextSelected : next.selectedRaw = raw :=
    GenuineSearch.retagBoundary_selectedRaw base c current growth target raw
      hraw htarget hdirection hgap
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
  exact {
    next := next
    selectedRaw := hnextSelected
    reaches := hreachesNext
    immortal := FullTM0.ImmortalFrom.of_reaches himmortal hreachesNext
    distance_eq := rfl }

/-! ## Final-boundary clock handoff -/

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
  -- The clock has no body route: validation reaches the test directly, and
  -- immortality then selects exactly one of its positive and zero branches.
  have hread : current.foundTape.read = boundarySymbol 4 :=
    outwardFour_foundTape_read current growth source
      (.decrement .clock ifZero ifPositive) hraw
  let testRule : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot, .boundary 4,
      directRef growth source branchDirectSlot, .left⟩
  have htestRule : testRule ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
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
  · -- The blank branch enters the first positive shift at boundary `4`.
    have hpositiveStep : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          current.foundTape.move (orient growth .left)⟩
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          current.foundTape⟩ := by
      rw [hback] at hpositiveStepRaw
      exact hpositiveStepRaw
    have hpositiveEntry : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          current.foundTape⟩ :=
      hbranch.trans hpositiveStep
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
    have entered := retaggedBranch base c current growth 4 raw hrawMem
      htarget hdirection hgap hcurrentDirection hread himmortal (by
        simpa only [raw,
          CounterControlGenuineDecrementEntry.firstDecrementShiftRaw,
          RawCommand.address] using hpositiveEntry)
    have hcommand : entered.next.selectedRaw ∈
        decrementShiftCommands growth source .clock := by
      rw [entered.selectedRaw]
      exact CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_mem
        growth source .clock
    rcases
        CounterControlDecrementShiftContinuation.foundMonotoneGuardedEntryOutcome_of_decrementShift
          base c hmortal entered.next growth source .clock ifZero ifPositive
          hrule hcommand entered.immortal with ⟨outcome⟩
    exact ⟨OutwardInstructionHandoff.ofMonotone entered.reaches
      (by rw [entered.distance_eq]) outcome⟩
  · -- The boundary-`3` branch enters the marker-preserving zero recovery.
    have hzeroStep : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          current.foundTape.move (orient growth .left)⟩
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          current.foundTape⟩ := by
      rw [hback] at hzeroStepRaw
      exact hzeroStepRaw
    have hzeroEntry : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          current.foundTape⟩ :=
      hbranch.trans hzeroStep
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
    have entered := retaggedBranch base c current growth 4 raw hrawMem
      htarget hdirection hgap hcurrentDirection hread himmortal (by
        simpa only [raw,
          CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw,
          RawCommand.address] using hzeroEntry)
    have hcommand : entered.next.selectedRaw ∈
        routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero .clock) := by
      rw [entered.selectedRaw]
      exact CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_mem
        growth source .clock ifZero
    rcases CounterControlGenuineRouteEmbedding.zeroRecovery_logical_of_rule
        base c hmortal entered.next entered.immortal growth source .clock ifZero
        ifPositive hrule hcommand with ⟨outcome⟩
    exact ⟨OutwardInstructionHandoff.ofMonotone entered.reaches
      (by rw [entered.distance_eq]) outcome⟩

end

end CounterControlGenuineValidationOutwardDecrementClock
end Hooper
end Kari
end LeanWang
