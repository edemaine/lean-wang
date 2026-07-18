/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrement
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrementClock

/-!
# Arbitrary outward validation suffix followed by a decrement

This module retains the exact tape geometry between an arbitrary outward
validation caller and either branch of the selected decrement.  The final
boundary-`4` cases are already discharged by the two specialized modules;
the packages below isolate the common body route, test, and branch used by
the earlier validation positions.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardDecrementSuffix

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGenuineValidation
open CounterControlGenuineValidationOutwardSuffix
open CounterControlRouteSuffixMortality CounterControlValidationMortality

noncomputable section

set_option maxRecDepth 10000

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private theorem immortalFrom_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {first second : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) first)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second) :
    FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) second := by
  rw [FullTM0.HaltsFrom.immortalFrom_iff_not] at himmortal ⊢
  intro hhalts
  exact himmortal (FullTM0.HaltsFrom.of_reaches hreach hhalts)

/-- Exact preserving route from the boundary-`4` body entry to the boundary
immediately after the selected register.  For the clock this route is empty.
-/
structure BodyRouteEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)) : Type where
  finish : FullTM0.Tape (Symbol numTags)
  tailGaps : RouteTailGaps growth
    (AnchoredCounterGeometry.routeToDecrementStart register)
    suffix.progress.suffix.finish finish
  finish_read : finish.read = boundarySymbol
    (MarkerSchedule.decrementStartBoundary register)
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    ⟨resolve base c (directRef growth source testDirectSlot), finish⟩

/-- The decrement-entry direct rule installed at boundary `4` for every
non-clock register. -/
private theorem routeEntryRule_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hregister : register ≠ .clock) :
    RawDirectRule.mk growth
      (directRef growth source bodyDirectBase) (.boundary 4)
      (searchRef growth source bodySearchBase) .left ∈ rawDirectRules := by
  apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
    growth hrule
  cases register with
  | left =>
      simp [directRulesForRule, decrementRules,
        AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
      exact Or.inr (Or.inl rfl)
  | right =>
      simp [directRulesForRule, decrementRules,
        AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
      exact Or.inr (Or.inl rfl)
  | temp =>
      simp [directRulesForRule, decrementRules,
        AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
      exact Or.inr (Or.inl rfl)
  | clock => exact False.elim (hregister rfl)

/-- All generated preserving searches in the decrement-entry route belong
to the selected instruction. -/
private theorem routeCommand_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (raw : RawCommand)
    (hraw : raw ∈ routeCommandsAux growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    raw ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, decrementCommands, hraw]

/-- All one-cell continuations in the decrement-entry route belong to the
selected instruction. -/
private theorem routeContinuation_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (rule : RawDirectRule)
    (hmem : rule ∈ routeContinuationRules growth source bodySearchBase
      (bodyDirectBase + 1)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    rule ∈ rawDirectRules := by
  apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
    growth hrule
  simp [directRulesForRule, decrementRules, hmem]

/-- Execute the whole route from an arbitrary outward validation suffix.
The proof separates the empty clock route from the three routes whose first
leg searches inward for boundary `3`. -/
theorem bodyRouteEnd_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (BodyRouteEnd current growth source register ifZero ifPositive
      suffix) := by
  cases register with
  | clock =>
      refine ⟨⟨suffix.progress.suffix.finish, ?_, ?_, ?_⟩⟩
      · exact .nil _
      · simpa [MarkerSchedule.decrementStartBoundary] using
          suffix.finish_read
      · simpa [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
          using suffix.reaches_bodyEntry
  | left =>
      let entryRule : RawDirectRule :=
        ⟨growth, directRef growth source bodyDirectBase, .boundary 4,
          searchRef growth source bodySearchBase, .left⟩
      have hentryRule : entryRule ∈ rawDirectRules := by
        exact routeEntryRule_mem growth source .left ifZero ifPositive hrule
          (by decide)
      have hmatch : entryRule.read.Matches
          suffix.progress.suffix.finish.read := by
        simpa [entryRule, RawRead.Matches] using suffix.finish_read
      have hentryLocal := CounterControlDirectSemantics.reaches_directRule
        base c entryRule hentryRule suffix.progress.suffix.finish hmatch
      have hentryDirect : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩
          ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
            suffix.progress.suffix.finish.move (orient growth .left)⟩ := by
        change FullTM0.Reaches
          (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
        simpa [entryRule, searchRef, resolve] using hentryLocal
      have hbody : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) (foundCfg current)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩ := by
        simpa [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
          using suffix.reaches_bodyEntry
      have hentry := hbody.trans hentryDirect
      rcases CounterControlValidationMortality.reaches_routeGaps_of_immortal
          base c hmortal himmortal growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          ⟨3, .left⟩ [⟨2, .left⟩, ⟨1, .left⟩]
          (suffix.progress.suffix.finish.move (orient growth .left)) hentry
          (routeCommand_mem growth source .left ifZero ifPositive hrule)
          (routeContinuation_mem growth source .left ifZero ifPositive hrule)
        with ⟨finish, trace, reaches⟩
      refine ⟨⟨finish, .cons ⟨3, .left⟩ [⟨2, .left⟩, ⟨1, .left⟩]
        suffix.progress.suffix.finish finish trace, ?_, reaches⟩⟩
      exact CounterControlGuardedDecrementEntry.routeGaps_finish_read trace
        (by simp)
  | right =>
      let entryRule : RawDirectRule :=
        ⟨growth, directRef growth source bodyDirectBase, .boundary 4,
          searchRef growth source bodySearchBase, .left⟩
      have hentryRule : entryRule ∈ rawDirectRules := by
        exact routeEntryRule_mem growth source .right ifZero ifPositive hrule
          (by decide)
      have hmatch : entryRule.read.Matches
          suffix.progress.suffix.finish.read := by
        simpa [entryRule, RawRead.Matches] using suffix.finish_read
      have hentryLocal := CounterControlDirectSemantics.reaches_directRule
        base c entryRule hentryRule suffix.progress.suffix.finish hmatch
      have hentryDirect : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩
          ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
            suffix.progress.suffix.finish.move (orient growth .left)⟩ := by
        change FullTM0.Reaches
          (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
        simpa [entryRule, searchRef, resolve] using hentryLocal
      have hbody : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) (foundCfg current)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩ := by
        simpa [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
          using suffix.reaches_bodyEntry
      have hentry := hbody.trans hentryDirect
      rcases CounterControlValidationMortality.reaches_routeGaps_of_immortal
          base c hmortal himmortal growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          ⟨3, .left⟩ [⟨2, .left⟩]
          (suffix.progress.suffix.finish.move (orient growth .left)) hentry
          (routeCommand_mem growth source .right ifZero ifPositive hrule)
          (routeContinuation_mem growth source .right ifZero ifPositive hrule)
        with ⟨finish, trace, reaches⟩
      refine ⟨⟨finish, .cons ⟨3, .left⟩ [⟨2, .left⟩]
        suffix.progress.suffix.finish finish trace, ?_, reaches⟩⟩
      exact CounterControlGuardedDecrementEntry.routeGaps_finish_read trace
        (by simp)
  | temp =>
      let entryRule : RawDirectRule :=
        ⟨growth, directRef growth source bodyDirectBase, .boundary 4,
          searchRef growth source bodySearchBase, .left⟩
      have hentryRule : entryRule ∈ rawDirectRules := by
        exact routeEntryRule_mem growth source .temp ifZero ifPositive hrule
          (by decide)
      have hmatch : entryRule.read.Matches
          suffix.progress.suffix.finish.read := by
        simpa [entryRule, RawRead.Matches] using suffix.finish_read
      have hentryLocal := CounterControlDirectSemantics.reaches_directRule
        base c entryRule hentryRule suffix.progress.suffix.finish hmatch
      have hentryDirect : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩
          ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
            suffix.progress.suffix.finish.move (orient growth .left)⟩ := by
        change FullTM0.Reaches
          (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
        simpa [entryRule, searchRef, resolve] using hentryLocal
      have hbody : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) (foundCfg current)
          ⟨resolve base c (directRef growth source bodyDirectBase),
            suffix.progress.suffix.finish⟩ := by
        simpa [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
          using suffix.reaches_bodyEntry
      have hentry := hbody.trans hentryDirect
      rcases CounterControlValidationMortality.reaches_routeGaps_of_immortal
          base c hmortal himmortal growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          ⟨3, .left⟩ []
          (suffix.progress.suffix.finish.move (orient growth .left)) hentry
          (routeCommand_mem growth source .temp ifZero ifPositive hrule)
          (routeContinuation_mem growth source .temp ifZero ifPositive hrule)
        with ⟨finish, trace, reaches⟩
      refine ⟨⟨finish, .cons ⟨3, .left⟩ []
        suffix.progress.suffix.finish finish trace, ?_, reaches⟩⟩
      exact CounterControlGuardedDecrementEntry.routeGaps_finish_read trace
        (by simp)

/-- Tape scanned by the two-way decrement branch after the test moves one
cell inward from the boundary after the selected register. -/
def BodyRouteEnd.branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    (route : BodyRouteEnd current growth source register ifZero ifPositive
      suffix) : FullTM0.Tape (Symbol numTags) :=
  route.finish.move (orient growth .left)

/-- Exact branch selected after the completed body route.  Both generated
searches begin on the unchanged route endpoint: the test's inward move and
the branch's outward move cancel. -/
inductive BodyBranchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)) : Type where
  | positive
      (route : BodyRouteEnd current growth source register ifZero ifPositive
        suffix)
      (read_blank : route.branchTape.read = blankSymbol)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          route.finish⟩)
  | zero
      (route : BodyRouteEnd current growth source register ifZero ifPositive
        suffix)
      (read_boundary : route.branchTape.read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          route.finish⟩)

/-- Execute the boundary test and the unique live branch after the retained
body route. -/
theorem bodyBranchOutcome_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive))
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (BodyBranchOutcome current growth source register ifZero
      ifPositive suffix) := by
  rcases bodyRouteEnd_of_immortal base c hmortal current growth source
      register ifZero ifPositive hrule suffix himmortal with ⟨route⟩
  let testRule : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot,
      .boundary (MarkerSchedule.decrementStartBoundary register),
      directRef growth source branchDirectSlot, .left⟩
  have htestRule : testRule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change testRule ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [testRule, decrementRules]
  have htestMatch : testRule.read.Matches route.finish.read := by
    simpa [testRule, RawRead.Matches] using route.finish_read
  have htestLocal := CounterControlDirectSemantics.reaches_directRule
    base c testRule htestRule route.finish htestMatch
  have htest : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot), route.finish⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        route.branchTape⟩ := by
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [testRule, BodyRouteEnd.branchTape] using htestLocal
  have hbranch : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source branchDirectSlot),
        route.branchTape⟩ :=
    route.reaches.trans htest
  have hread := CounterControlGenuineDecrementEntry.branchRead_of_reaches
    base c hrule route.branchTape hbranch himmortal
  have hback : route.branchTape.move (orient growth .right) = route.finish := by
    cases growth <;>
      simp [BodyRouteEnd.branchTape, orient, FullTM0.Tape.move]
  have hback' : route.branchTape.move growth = route.finish := by
    cases growth <;> simpa [orient] using hback
  rcases hread with hblank | hboundary
  · let branchRule : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot, .blank,
        searchRef growth source secondarySearchBase, .right⟩
    have hbranchRule : branchRule ∈ rawDirectRules := by
      apply
        CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
      change branchRule ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [branchRule, decrementRules]
    have hbranchMatch : branchRule.read.Matches route.branchTape.read := by
      simpa [branchRule, RawRead.Matches] using hblank
    have hpositiveLocal := CounterControlDirectSemantics.reaches_directRule
      base c branchRule hbranchRule route.branchTape hbranchMatch
    have hpositive : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          route.branchTape⟩
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          route.finish⟩ := by
      change FullTM0.Reaches
        (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
      simpa [branchRule, searchRef, resolve, hback'] using hpositiveLocal
    exact ⟨.positive route hblank (hbranch.trans hpositive)⟩
  · let branchRule : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot,
        .boundary (AnchoredCounterGeometry.registerGap register).castSucc,
        searchRef growth source zeroSearchBase, .right⟩
    have hbranchRule : branchRule ∈ rawDirectRules := by
      apply
        CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
          growth hrule
      change branchRule ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [branchRule, decrementRules]
    have hbranchMatch : branchRule.read.Matches route.branchTape.read := by
      simpa [branchRule, RawRead.Matches] using hboundary
    have hzeroLocal := CounterControlDirectSemantics.reaches_directRule
      base c branchRule hbranchRule route.branchTape hbranchMatch
    have hzero : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          route.branchTape⟩
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          route.finish⟩ := by
      change FullTM0.Reaches
        (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
      simpa [branchRule, searchRef, resolve, hback'] using hzeroLocal
    exact ⟨.zero route hboundary (hbranch.trans hzero)⟩

end

end CounterControlGenuineValidationOutwardDecrementSuffix
end Hooper
end Kari
end LeanWang
