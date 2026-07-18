/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrement
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardDecrementClock
import LeanWang.Kari.Hooper.CounterControlOutwardGapTransport
import LeanWang.Kari.Hooper.CounterControlRouteRoundtrip

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
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlSearchSystem CounterControlCoreFrame
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlParentEmbedding CounterControlPrefixInstructionResolution
open CounterControlGenuineValidation
open CounterControlGenuineValidationOutwardSuffix
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlResumedRouteEmbedding

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

/-! ## Reversing the retained outward route -/

private theorem routeTail_nil_finish
    {growth : Turing.Dir}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth [] start finish) : finish = start := by
  cases trace
  rfl

private theorem toFour_uncons
    {boundary : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToFour boundary route) (hne : boundary ≠ 4) :
    ∃ i : Fin 4, ∃ rest,
      boundary = i.castSucc ∧
      route = ⟨i.succ, .right⟩ :: rest ∧ ToFour i.succ rest := by
  cases hroute with
  | four => exact False.elim (hne rfl)
  | step i tail => exact ⟨i, _, rfl, rfl, tail⟩

private theorem toFour_nil_of_eq_four
    {boundary : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : ToFour boundary route) (heq : boundary = 4) : route = [] := by
  cases hroute with
  | four => rfl
  | step i tail =>
      have hval := congrArg Fin.val heq
      simp at hval
      omega

private theorem toFour_four
    {route : List MarkerValidation.Leg} (hroute : ToFour 4 route) :
    route = [] :=
  toFour_nil_of_eq_four hroute rfl

private theorem toFour_three
    {route : List MarkerValidation.Leg} (hroute : ToFour 3 route) :
    route = [⟨4, .right⟩] := by
  rcases toFour_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (3 : Fin 4) := by
    apply Fin.ext
    exact (congrArg Fin.val hi).symm
  subst i
  have hnil : rest = [] := by
    apply toFour_four
    simpa using hrest
  rw [hrouteEq, hnil]
  rfl

private theorem toFour_two
    {route : List MarkerValidation.Leg} (hroute : ToFour 2 route) :
    route = [⟨3, .right⟩, ⟨4, .right⟩] := by
  rcases toFour_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (2 : Fin 4) := by
    apply Fin.ext
    exact (congrArg Fin.val hi).symm
  subst i
  have htail : rest = [⟨4, .right⟩] := by
    apply toFour_three
    simpa using hrest
  rw [hrouteEq, htail]
  rfl

private theorem toFour_one
    {route : List MarkerValidation.Leg} (hroute : ToFour 1 route) :
    route = [⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩] := by
  rcases toFour_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (1 : Fin 4) := by
    apply Fin.ext
    exact (congrArg Fin.val hi).symm
  subst i
  have htail : rest = [⟨3, .right⟩, ⟨4, .right⟩] := by
    apply toFour_two
    simpa using hrest
  rw [hrouteEq, htail]
  rfl

private theorem toBoundary_uncons
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary source target
      route)
    (hne : source ≠ target) :
    ∃ i : Fin 4, ∃ rest,
      source = i.succ ∧
      route = ⟨i.castSucc, .left⟩ :: rest ∧
      CounterControlGuardedInwardRouteMargin.ToBoundary i.castSucc target
        rest := by
  cases hroute with
  | here => exact False.elim (hne rfl)
  | step i tail => exact ⟨i, _, rfl, rfl, tail⟩

private theorem toBoundary_target_le
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary source target
      route) : (target : Nat) ≤ (source : Nat) := by
  induction hroute with
  | here => exact Nat.le_refl _
  | step i tail ih =>
      exact ih.trans (by simp)

private theorem toBoundary_nil_of_eq
    {source target : Fin 5} {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary source target
      route)
    (heq : source = target) : route = [] := by
  cases hroute with
  | here => rfl
  | step i tail =>
      have hle := toBoundary_target_le tail
      have hval := congrArg Fin.val heq
      simp at hval hle
      omega

private theorem toBoundary_four_four
    {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary 4 4 route) :
    route = [] :=
  toBoundary_nil_of_eq hroute rfl

private theorem toBoundary_four_three
    {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary 4 3 route) :
    route = [⟨3, .left⟩] := by
  rcases toBoundary_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (3 : Fin 4) := by
    have hval := congrArg Fin.val hi
    apply Fin.ext
    simp at hval ⊢
    omega
  subst i
  have hnil : rest = [] := by
    apply toBoundary_nil_of_eq hrest
    rfl
  rw [hrouteEq, hnil]
  rfl

private theorem toBoundary_four_two
    {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary 4 2 route) :
    route = [⟨3, .left⟩, ⟨2, .left⟩] := by
  rcases toBoundary_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (3 : Fin 4) := by
    have hval := congrArg Fin.val hi
    apply Fin.ext
    simp at hval ⊢
    omega
  subst i
  rcases toBoundary_uncons hrest (by decide) with
    ⟨j, tail, hj, hrestEq, htail⟩
  have hj' : j = (2 : Fin 4) := by
    have hval := congrArg Fin.val hj
    apply Fin.ext
    simp at hval ⊢
    omega
  subst j
  have hnil : tail = [] := by
    apply toBoundary_nil_of_eq htail
    rfl
  rw [hrouteEq, hrestEq, hnil]
  rfl

private theorem toBoundary_four_one
    {route : List MarkerValidation.Leg}
    (hroute : CounterControlGuardedInwardRouteMargin.ToBoundary 4 1 route) :
    route = [⟨3, .left⟩, ⟨2, .left⟩, ⟨1, .left⟩] := by
  rcases toBoundary_uncons hroute (by decide) with
    ⟨i, rest, hi, hrouteEq, hrest⟩
  have hi' : i = (3 : Fin 4) := by
    have hval := congrArg Fin.val hi
    apply Fin.ext
    simp at hval ⊢
    omega
  subst i
  rcases toBoundary_uncons hrest (by decide) with
    ⟨j, tail, hj, hrestEq, htail⟩
  have hj' : j = (2 : Fin 4) := by
    have hval := congrArg Fin.val hj
    apply Fin.ext
    simp at hval ⊢
    omega
  subst j
  rcases toBoundary_uncons htail (by decide) with
    ⟨k, final, hk, htailEq, hfinal⟩
  have hk' : k = (1 : Fin 4) := by
    have hval := congrArg Fin.val hk
    apply Fin.ext
    simp at hval ⊢
    omega
  subst k
  have hnil : final = [] := by
    apply toBoundary_nil_of_eq hfinal
    rfl
  rw [hrouteEq, hrestEq, htailEq, hnil]
  rfl

/-- Cancel one outward preserving gap against the first leg of a later
inward route, retaining the inward tail at the original source tape. -/
private theorem cancelRouteLeg
    {growth : Turing.Dir} {source target : Fin 5}
    {rest : List MarkerValidation.Leg}
    {lower upper finish : FullTM0.Tape (Symbol numTags)}
    {distance : Nat}
    (lower_read : lower.read = boundarySymbol source)
    (outwardGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches
      (lower.move (orient growth .right)) (orient growth .right) distance)
    (upper_eq :
      (lower.move (orient growth .right)).moveN
        (orient growth .right) distance = upper)
    (inward : RouteTailGaps growth
      (⟨source, .left⟩ :: rest) upper finish) :
    RouteTailGaps growth rest lower finish := by
  rcases inward.uncons with ⟨reverseDistance, reverseGap, tail⟩
  let returned :=
    (upper.move (orient growth .left)).moveN
      (orient growth .left) reverseDistance
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hreverse : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary source).Matches
      ((((lower.move (orient growth .right)).moveN
          (orient growth .right) distance).move
        (NestingMachine.opposite (orient growth .right))))
      (NestingMachine.opposite (orient growth .right)) reverseDistance := by
    rw [hopposite, upper_eq]
    exact reverseGap
  have hreturned : returned = lower := by
    apply CounterControlRouteRoundtrip.reverseRouteLeg_found_eq lower_read
      outwardGap hreverse
    dsimp [returned]
    rw [← upper_eq, hopposite]
  change RouteTailGaps growth rest returned finish at tail
  rwa [hreturned] at tail

/-- Reverse a retained suffix from boundary `3` through boundary `4`. -/
private theorem roundtripFromThree
    {growth : Turing.Dir}
    {rest : List MarkerValidation.Leg}
    {start top finish : FullTM0.Tape (Symbol numTags)}
    (start_read : start.read = boundarySymbol 3)
    (outward : RouteTailGaps growth [⟨4, .right⟩] start top)
    (inward : RouteTailGaps growth (⟨3, .left⟩ :: rest) top finish) :
    RouteTailGaps growth rest start finish := by
  rcases outward.uncons with ⟨distance, gap, tail⟩
  have htop := routeTail_nil_finish tail
  apply cancelRouteLeg start_read gap htop.symm inward

/-- Reverse a retained suffix from boundary `2` through boundary `4`. -/
private theorem roundtripFromTwo
    {growth : Turing.Dir}
    {rest : List MarkerValidation.Leg}
    {start top finish : FullTM0.Tape (Symbol numTags)}
    (start_read : start.read = boundarySymbol 2)
    (outward : RouteTailGaps growth
      [⟨3, .right⟩, ⟨4, .right⟩] start top)
    (inward : RouteTailGaps growth
      (⟨3, .left⟩ :: ⟨2, .left⟩ :: rest) top finish) :
    RouteTailGaps growth rest start finish := by
  rcases outward.uncons with ⟨distance, gap, tail⟩
  let found :=
    (start.move (orient growth .right)).moveN
      (orient growth .right) distance
  have found_read : found.read = boundarySymbol 3 := by
    simpa [found, FullTM0.Tape.read_moveN, Target.Matches] using gap.marked
  have returned := roundtripFromThree found_read tail inward
  change RouteTailGaps growth (⟨2, .left⟩ :: rest) found finish
    at returned
  apply cancelRouteLeg start_read gap rfl returned

/-- Reverse a retained suffix from boundary `1` through boundary `4`. -/
private theorem roundtripFromOne
    {growth : Turing.Dir}
    {rest : List MarkerValidation.Leg}
    {start top finish : FullTM0.Tape (Symbol numTags)}
    (start_read : start.read = boundarySymbol 1)
    (outward : RouteTailGaps growth
      [⟨2, .right⟩, ⟨3, .right⟩, ⟨4, .right⟩] start top)
    (inward : RouteTailGaps growth
      (⟨3, .left⟩ :: ⟨2, .left⟩ :: ⟨1, .left⟩ :: rest)
      top finish) :
    RouteTailGaps growth rest start finish := by
  rcases outward.uncons with ⟨distance, gap, tail⟩
  let found :=
    (start.move (orient growth .right)).moveN
      (orient growth .right) distance
  have found_read : found.read = boundarySymbol 2 := by
    simpa [found, FullTM0.Tape.read_moveN, Target.Matches] using gap.marked
  have returned := roundtripFromTwo found_read tail inward
  change RouteTailGaps growth (⟨1, .left⟩ :: rest) found finish
    at returned
  apply cancelRouteLeg start_read gap rfl returned

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

/-- If the original outward caller found the boundary where the decrement
body route ends, the outward and inward preserving routes cancel exactly.
-/
theorem BodyRouteEnd.finish_eq_current_of_boundary_eq
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    (route : BodyRouteEnd current growth source register ifZero ifPositive
      suffix)
    (hboundary : suffix.index.succ =
      MarkerSchedule.decrementStartBoundary register) :
    route.finish = current.foundTape := by
  generalize hindex : suffix.index = index
  fin_cases index
  · have hregister : register = .left := by
      cases register <;>
        simp_all [MarkerSchedule.decrementStartBoundary]
    subst register
    have htoFour : ToFour 1 suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_one htoFour
    have hout := suffix.tailGaps
    rw [hremaining] at hout
    have hrouteExact := toBoundary_four_one
      (CounterControlGuardedInwardRouteMargin.routeToDecrementStart_toBoundary
        .left)
    have hin' := route.tailGaps
    rw [hrouteExact] at hin'
    have hin : RouteTailGaps growth
        [⟨3, .left⟩, ⟨2, .left⟩, ⟨1, .left⟩]
        suffix.progress.suffix.finish route.finish := by
      exact hin'
    have hread : current.foundTape.read = boundarySymbol 1 := by
      simpa [hindex] using suffix.current_read
    exact routeTail_nil_finish (roundtripFromOne hread hout hin)
  · have hregister : register = .right := by
      cases register <;>
        simp_all [MarkerSchedule.decrementStartBoundary]
    subst register
    have htoFour : ToFour 2 suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_two htoFour
    have hout := suffix.tailGaps
    rw [hremaining] at hout
    have hrouteExact := toBoundary_four_two
      (CounterControlGuardedInwardRouteMargin.routeToDecrementStart_toBoundary
        .right)
    have hin' := route.tailGaps
    rw [hrouteExact] at hin'
    have hin : RouteTailGaps growth [⟨3, .left⟩, ⟨2, .left⟩]
        suffix.progress.suffix.finish route.finish := by
      exact hin'
    have hread : current.foundTape.read = boundarySymbol 2 := by
      simpa [hindex] using suffix.current_read
    exact routeTail_nil_finish (roundtripFromTwo hread hout hin)
  · have hregister : register = .temp := by
      cases register <;>
        simp_all [MarkerSchedule.decrementStartBoundary]
    subst register
    have htoFour : ToFour 3 suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_three htoFour
    have hout := suffix.tailGaps
    rw [hremaining] at hout
    have hrouteExact := toBoundary_four_three
      (CounterControlGuardedInwardRouteMargin.routeToDecrementStart_toBoundary
        .temp)
    have hin' := route.tailGaps
    rw [hrouteExact] at hin'
    have hin : RouteTailGaps growth [⟨3, .left⟩]
        suffix.progress.suffix.finish route.finish := by
      exact hin'
    have hread : current.foundTape.read = boundarySymbol 3 := by
      simpa [hindex] using suffix.current_read
    exact routeTail_nil_finish (roundtripFromThree hread hout hin)
  · have hregister : register = .clock := by
      cases register <;>
        simp_all [MarkerSchedule.decrementStartBoundary]
    subst register
    have htoFour : ToFour 4 suffix.progress.suffix.remaining := by
      simpa [hindex] using suffix.remaining_toFour
    have hremaining := toFour_four htoFour
    have hout := suffix.tailGaps
    rw [hremaining] at hout
    have htop : suffix.progress.suffix.finish = current.foundTape :=
      routeTail_nil_finish hout
    have hrouteExact := toBoundary_four_four
      (CounterControlGuardedInwardRouteMargin.routeToDecrementStart_toBoundary
        .clock)
    have hin' := route.tailGaps
    rw [hrouteExact] at hin'
    have hin : RouteTailGaps growth [] suffix.progress.suffix.finish
        route.finish := by
      exact hin'
    exact (routeTail_nil_finish hin).trans htop

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

/-! ## Exact generated branch searches -/

/-- Distance-zero guarded first shift produced by the positive branch. -/
structure PositiveSearchEntry
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)) : Type where
  route : BodyRouteEnd current growth source register ifZero ifPositive suffix
  read_blank : route.branchTape.read = blankSymbol
  next : CounterControlGuardedSearch.GuardedSearch base c
  selectedRaw_eq : next.current.selectedRaw =
    CounterControlGenuineDecrementEntry.firstDecrementShiftRaw
      growth source register
  selectedRaw_mem : next.current.selectedRaw ∈
    decrementShiftCommands growth source register
  outer_eq : next.current.outer = route.finish
  distance_eq : next.current.distance = 0
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) next.current.cfg

/-- Distance-zero first recovery search produced by the zero branch. -/
structure ZeroSearchEntry
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)) : Type where
  route : BodyRouteEnd current growth source register ifZero ifPositive suffix
  read_boundary : route.branchTape.read = boundarySymbol
    (AnchoredCounterGeometry.registerGap register).castSucc
  next : GenuineSearch base c
  selectedRaw_eq : next.selectedRaw =
    CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw
      growth source register ifZero
  selectedRaw_mem : next.selectedRaw ∈
    routeCommandsAux growth source zeroSearchBase zeroDirectBase
      (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register)
  outer_eq : next.outer = route.finish
  distance_eq : next.distance = 0
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) next.cfg

/-- Generated-search form of either exact body branch. -/
inductive BodyBranchSearchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)) : Type where
  | positive (entry : PositiveSearchEntry current growth source register
      ifZero ifPositive suffix)
  | zero (entry : ZeroSearchEntry current growth source register
      ifZero ifPositive suffix)

/-- Retag either branch endpoint with the first generated command of the
selected continuation. -/
theorem bodyBranchSearchOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (outcome : BodyBranchOutcome current growth source register ifZero
      ifPositive suffix) :
    Nonempty (BodyBranchSearchOutcome current growth source register ifZero
      ifPositive suffix) := by
  cases outcome with
  | positive route hblank hreach =>
      let raw := CounterControlGenuineDecrementEntry.firstDecrementShiftRaw
        growth source register
      have hraw : raw ∈ rawCommands :=
        CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_mem_rawCommands
          growth source register ifZero ifPositive hrule
      have hmatch :
          (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
            route.finish.read := by
        rw [CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_target]
        simpa [Target.Matches] using route.finish_read
      let genuine : GenuineSearch base c :=
        CounterControlGenuineDecrementEntry.immediateSearch base c raw hraw
          route.finish hmatch
      have hdirection : genuine.direction = orient growth .right := by
        rw [CounterControlGenuineDecrementEntry.immediateSearch_direction,
          CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_direction]
      let next : CounterControlGuardedSearch.GuardedSearch base c := {
        current := genuine
        guard := by
          change (genuine.outer.move
            (NestingMachine.opposite genuine.direction)).read = blankSymbol
          rw [hdirection]
          have hopposite : NestingMachine.opposite (orient growth .right) =
              orient growth .left := by
            cases growth <;> rfl
          rw [hopposite]
          exact hblank }
      have hreach' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) (foundCfg current)
          genuine.cfg := by
        rw [CounterControlGenuineDecrementEntry.immediateSearch_cfg]
        exact hreach
      refine ⟨.positive {
        route := route
        read_blank := hblank
        next := next
        selectedRaw_eq := ?_
        selectedRaw_mem := ?_
        outer_eq := rfl
        distance_eq := rfl
        reaches := hreach' }⟩
      · exact
          CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
            base c raw hraw route.finish hmatch
      · rw [show next.current.selectedRaw = raw by
            exact
              CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
                base c raw hraw route.finish hmatch]
        exact
          CounterControlGenuineDecrementEntry.firstDecrementShiftRaw_mem
            growth source register
  | zero route hboundary hreach =>
      let raw := CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw
        growth source register ifZero
      have hraw : raw ∈ rawCommands :=
        CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_mem_rawCommands
          growth source register ifZero ifPositive hrule
      have hmatch :
          (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
            route.finish.read := by
        rw [CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_target]
        simpa [Target.Matches] using route.finish_read
      let next : GenuineSearch base c :=
        CounterControlGenuineDecrementEntry.immediateSearch base c raw hraw
          route.finish hmatch
      have hreach' : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c) (foundCfg current)
          next.cfg := by
        rw [CounterControlGenuineDecrementEntry.immediateSearch_cfg]
        exact hreach
      refine ⟨.zero {
        route := route
        read_boundary := hboundary
        next := next
        selectedRaw_eq := ?_
        selectedRaw_mem := ?_
        outer_eq := rfl
        distance_eq := rfl
        reaches := hreach' }⟩
      · exact
          CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
            base c raw hraw route.finish hmatch
      · rw [show next.selectedRaw = raw by
            exact
              CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw
                base c raw hraw route.finish hmatch]
        exact CounterControlGenuineDecrementEntry.firstZeroRecoveryRaw_mem
          growth source register ifZero

/-! ## Centered logical endpoints -/

/-- Completed positive shift endpoint, retaining the old body route and the
centered reconstructed core. -/
structure PositiveCenteredEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive))
    (entry : PositiveSearchEntry current growth source register ifZero
      ifPositive suffix) : Type where
  direct : CounterControlGuardedShiftCompletion.DecrementPositiveDirectHandoff
    entry.next growth source register ifZero ifPositive
  endpoint : CounterControlGuardedShiftEmbedding.DecrementPositiveCenteredEnd
    entry.next growth source register ifZero ifPositive direct
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) endpoint.core.cfg

/-- Complete the positive shift branch and reconstruct its centered logical
core. -/
theorem PositiveSearchEntry.centeredEnd_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    (entry : PositiveSearchEntry current growth source register ifZero
      ifPositive suffix)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (PositiveCenteredEnd current growth source register ifZero
      ifPositive suffix entry) := by
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) entry.next.current.cfg :=
    immortalFrom_of_reaches base c himmortal entry.reaches
  have hfound := reaches_foundCfg_of_immortal entry.next.current himmortalNext
  have himmortalFound := immortalFrom_of_reaches base c himmortalNext hfound
  rcases CounterControlGuardedSearch.GuardedSearch.decrementShift_suffix_of_immortal
      base c hmortal entry.next growth source register ifZero ifPositive
      hrule entry.selectedRaw_mem himmortalFound with ⟨shiftSuffix⟩
  rcases CounterControlGuardedShiftCompletion.decrementPositiveDirectHandoff
      base c entry.next growth source register ifZero ifPositive hrule
      shiftSuffix with ⟨direct⟩
  rcases CounterControlGuardedShiftEmbedding.decrementPositiveCenteredEnd
      base c hmortal entry.next himmortalFound growth source register ifZero
      ifPositive direct with ⟨endpoint⟩
  exact ⟨⟨direct, endpoint,
    entry.reaches.trans (hfound.trans endpoint.reaches)⟩⟩

/-- Completed zero-recovery endpoint, retaining the unchanged selected
boundary tape at its canonical coordinate in the reconstructed core. -/
structure ZeroCenteredEnd
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (suffix : Suffix current growth source
      (.decrement register ifZero ifPositive))
    (entry : ZeroSearchEntry current growth source register ifZero ifPositive
      suffix) : Type where
  core : LogicalCore base c
  core_represents : CoreRepresents core.registers growth core.tape
  route_finish : entry.route.finish =
    atLogical growth core.tape
      (boundaryOffset core.registers
        (MarkerSchedule.decrementStartBoundary register))
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) core.cfg

/-- Follow zero recovery through its preserving route and reconstruct the
selected body-route boundary in the resulting logical core. -/
theorem ZeroSearchEntry.centeredEnd_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    (entry : ZeroSearchEntry current growth source register ifZero ifPositive
      suffix)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (ZeroCenteredEnd current growth source register ifZero
      ifPositive suffix entry) := by
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) entry.next.cfg :=
    immortalFrom_of_reaches base c himmortal entry.reaches
  have hfound := reaches_foundCfg_of_immortal entry.next himmortalNext
  have himmortalFound := immortalFrom_of_reaches base c himmortalNext hfound
  have hcommands : ∀ command,
      command ∈ routeCommandsAux growth source zeroSearchBase zeroDirectBase
          (.logical growth ifZero)
          (AnchoredCounterGeometry.routeFromZero register) →
        command ∈ rawCommands := by
    intro command hmem
    exact CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule (by simp [commandsForRule, decrementCommands, hmem])
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source zeroSearchBase
          zeroDirectBase (AnchoredCounterGeometry.routeFromZero register) →
        rule ∈ rawDirectRules := by
    intro rule hmem
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    simp [directRulesForRule, decrementRules, hmem]
  rcases CounterControlGenuineRouteEmbedding.progressedRoute base c hmortal
      entry.next himmortalFound growth source zeroSearchBase zeroDirectBase
      (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register) entry.selectedRaw_mem
      hcommands hcontinuations with ⟨progress⟩
  have himmortalLogical := immortalFrom_of_reaches base c himmortalFound
    progress.reaches
  change FullTM0.ImmortalFrom
    (CounterControlNestingBridge.machine base c)
    ⟨logicalState base c growth ifZero, progress.suffix.finish⟩
      at himmortalLogical
  have htargetState : ifZero < logicalSpan :=
    state_lt_logicalSpan
      (CounterControlAbstractTrace.target_mem_programStates hrule
        (by simp [instructionTargets]))
  rcases
      CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
        base c hmortal growth ifZero htargetState progress.suffix.finish
        himmortalLogical with
    ⟨instruction, registers, coreTape, limit, target, _hrule, hcore,
      hcoreBefore, hrunway, htarget, hcenter, _hbody⟩
  let represented : CoreTargetRepresents registers growth limit target
      coreTape := {
    toCorePrefixRepresents := {
      toCoreRepresents := hcore
      core_before_limit := hcoreBefore
      runway := hrunway }
    target_matches := htarget }
  let core : LogicalCore base c := {
    growth := growth
    source := ifZero
    source_lt := htargetState
    registers := registers
    tape := coreTape
    limit := limit
    target := target
    represented := represented }
  rcases routeFromZero_toFour register with ⟨routeSource, hroute⟩
  rcases hroute.position progress.suffix.route_eq with
    ⟨i, hcurrent, htail⟩
  have hread : entry.next.foundTape.read = boundarySymbol i.succ := by
    have hread' := progress.current_read
    rw [hcurrent] at hread'
    exact hread'
  have hentryFound : entry.next.foundTape = entry.route.finish := by
    rw [GenuineSearch.foundTape, entry.distance_eq, FullTM0.Tape.moveN_zero,
      entry.outer_eq]
  have hstartLabel : i.succ =
      MarkerSchedule.decrementStartBoundary register := by
    apply (boundarySymbol_injective _ _).mp
    exact hread.symm.trans
      ((congrArg FullTM0.Tape.read hentryFound).trans
        entry.route.finish_read)
  have hfoundBoundary : entry.next.foundTape =
      atLogical growth coreTape (boundaryOffset registers i.succ) := by
    exact htail.start_eq hcore hread progress.suffix.tailGaps hcenter
  have hrouteFinish : entry.route.finish =
      atLogical growth coreTape
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register)) := by
    rw [← hentryFound, hfoundBoundary, hstartLabel]
  have hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) core.cfg := by
    have hrun := entry.reaches.trans (hfound.trans progress.reaches)
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨logicalState base c growth ifZero, progress.suffix.finish⟩ at hrun
    rw [hcenter] at hrun
    simpa [core, LogicalCore.cfg, LogicalCore.frame,
      LogicalCore.abstract, prefixLogicalCfg] using hrun
  exact ⟨⟨core, hcore, hrouteFinish, hreaches⟩⟩

/-- Zero recovery changes no marker.  Reverse its body route to recover
canonical boundary `4`, then reverse the retained validation suffix to put
the original found boundary at its canonical coordinate. -/
theorem ZeroCenteredEnd.distance_lt_layoutEnd
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    {suffix : Suffix current growth source
      (.decrement register ifZero ifPositive)}
    {entry : ZeroSearchEntry current growth source register ifZero ifPositive
      suffix}
    (endpoint : ZeroCenteredEnd current growth source register ifZero
      ifPositive suffix entry) :
    current.distance < layoutEnd endpoint.core.registers := by
  have hbodyStart : suffix.progress.suffix.finish =
      atLogical growth endpoint.core.tape
        (boundaryOffset endpoint.core.registers 4) := by
    exact
      (CounterControlGuardedInwardRouteMargin.routeToDecrementStart_toBoundary
        register).start_eq endpoint.core_represents suffix.finish_read
          entry.route.tailGaps endpoint.route_finish
  have hboundaryFour : suffix.progress.suffix.finish =
      atLogical growth endpoint.core.tape
        (layoutEnd endpoint.core.registers) := by
    simpa [boundaryOffset_four] using hbodyStart
  have hcurrentFound : current.foundTape =
      atLogical growth endpoint.core.tape
        (boundaryOffset endpoint.core.registers suffix.index.succ) := by
    exact suffix.remaining_toFour.start_eq endpoint.core_represents
      suffix.current_read suffix.tailGaps hboundaryFour
  exact rightGap_distance_lt_layoutEnd endpoint.core_represents suffix.index
    current.distance suffix.current_gap
      (suffix.current_foundTape.trans hcurrentFound)

end

end CounterControlGenuineValidationOutwardDecrementSuffix
end Hooper
end Kari
end LeanWang
