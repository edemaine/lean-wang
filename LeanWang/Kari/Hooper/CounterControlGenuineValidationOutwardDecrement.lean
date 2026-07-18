/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutward
import LeanWang.Kari.Hooper.CounterControlDecrementEntryContinuation
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap

/-!
# Final outward validation followed by a decrement

For a non-clock decrement, the final outward validation command enters the
first leftward route search from boundary `4`.  Immortality supplies its
finite gap.  The old outward gap cannot cross the boundary found by this
reverse search, so its distance is no larger.  The completed arbitrary
decrement-entry continuation can therefore be transported back to the
original validation caller.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardDecrement

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlGenuineValidation

noncomputable section

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

private theorem outwardFour_gap
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source instruction) .preserve) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches current.outer
      (orient growth .right) current.distance := by
  have hgap := current.gap
  rw [← current.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target,
    Command.searchDirection] using hgap

private theorem outwardFour_direction
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source instruction) .preserve) :
    current.direction = orient growth .right := by
  have hdirection := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection]
    at hdirection
  rw [hraw] at hdirection
  exact hdirection.symm

private theorem outwardFour_foundTape_read
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source instruction) .preserve) :
    current.foundTape.read = boundarySymbol 4 := by
  have hmatch := current.selectedRaw_target_matches_foundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target, Target.Matches] using hmatch

/-- Common proof for the three nonempty decrement-entry routes. -/
private theorem outwardFour_nonemptyDecrement_handoff
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : ValidationEnd current growth source
      (.decrement register ifZero ifPositive))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source
          (.decrement register ifZero ifPositive)) .preserve)
    (success : ControlRef)
    (hcommand : RawCommand.boundaryNavigation
      ⟨growth, source, bodySearchBase⟩ 3 .left success .preserve ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register))
    (hbodyEntry : bodyEntry growth source
        (.decrement register ifZero ifPositive) =
      directRef growth source bodyDirectBase)
    (hentryRule : RawDirectRule.mk growth
      (directRef growth source bodyDirectBase) (.boundary 4)
      (searchRef growth source bodySearchBase) .left ∈ rawDirectRules)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current
      (OutwardObligation.four progress hraw)) := by
  let raw : RawCommand := .boundaryNavigation
    ⟨growth, source, bodySearchBase⟩ 3 .left success .preserve
  have hrawCommands : raw ∈ rawCommands := by
    apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
      growth hrule
    simp [commandsForRule, decrementCommands, raw, hcommand]
  have hread : current.foundTape.read = boundarySymbol 4 :=
    outwardFour_foundTape_read current growth source
      (.decrement register ifZero ifPositive) hraw
  let entryRule : RawDirectRule :=
    ⟨growth, directRef growth source bodyDirectBase, .boundary 4,
      searchRef growth source bodySearchBase, .left⟩
  have hmatch : entryRule.read.Matches current.foundTape.read := by
    simpa [entryRule, RawRead.Matches] using hread
  have hdirectLocal := CounterControlDirectSemantics.reaches_directRule
    base c entryRule (by simpa [entryRule] using hentryRule)
      current.foundTape hmatch
  have hdirect : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source bodyDirectBase),
        current.foundTape⟩
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape.move (orient growth .left)⟩ := by
    change FullTM0.Reaches
      (FiniteTM0.machine (CounterControlPlan.table base c)) _ _
    simpa [entryRule, searchRef, resolve] using hdirectLocal
  have hbody := outwardFour_reaches_bodyEntry progress hraw
  have hentry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape.move (orient growth .left)⟩ := by
    have hbody' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c) (foundCfg current)
        ⟨resolve base c (directRef growth source bodyDirectBase),
          current.foundTape⟩ := by
      simpa [hbodyEntry] using hbody
    exact hbody'.trans hdirect
  have himmortalEntry : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape.move (orient growth .left)⟩ :=
    immortalFrom_of_reaches base c himmortal hentry
  rcases
      CounterControlGeneratedSearchGap.boundaryNavigation_gap_of_immortal
        base c hmortal ⟨growth, source, bodySearchBase⟩ 3 .left success
        .preserve (by simpa [raw] using hrawCommands)
        (current.foundTape.move (orient growth .left)) himmortalEntry with
    ⟨distance, hgap⟩
  let search : Search := CounterControlCommandAt.rawTag raw hrawCommands
  let next : GenuineSearch base c := {
    search := search
    outer := current.foundTape.move (orient growth .left)
    distance := distance
    gap := by
      have hcompiled : command base c search =
          CounterControlCommandAt.compileRawCommand base c raw
            hrawCommands := by
        rfl
      rw [hcompiled, CounterControlCommandAt.compileRawCommand_spec]
      simpa [raw, CounterControlCommandAt.compileRawAtTag,
        compileNavigationAction, Command.target,
        Command.searchDirection] using hgap }
  have hnextCfg : next.cfg =
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape.move (orient growth .left)⟩ := by
    change (searchSystem base c).startCfg search
      (current.foundTape.move (orient growth .left)) = _
    change (⟨CounterControlSearchSystem.commandOffset base c search,
      current.foundTape.move (orient growth .left)⟩ :
        FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [show rawCommands.get search = raw by
      exact CounterControlCommandAt.rawCommands_get_rawTag raw hrawCommands]
    rfl
  have hnextSelected : next.selectedRaw = raw := by
    change rawCommands.get search = raw
    exact CounterControlCommandAt.rawCommands_get_rawTag raw hrawCommands
  have hnextCommand : next.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register) := by
    rw [hnextSelected]
    exact hcommand
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) next.cfg := by
    rw [hnextCfg]
    exact himmortalEntry
  have hfoundNext := reaches_foundCfg_of_immortal next himmortalNext
  have himmortalFoundNext := immortalFrom_of_reaches base c himmortalNext
    hfoundNext
  rcases
      CounterControlDecrementEntryContinuation.foundMonotoneGuardedEntryOutcome_of_decrementEntry
        base c hmortal next growth source register ifZero ifPositive hrule
        hnextCommand himmortalFoundNext with
    ⟨outcome⟩
  have hcurrentGap := outwardFour_gap current growth source
    (.decrement register ifZero ifPositive) hraw
  have hdirection := outwardFour_direction current growth source
    (.decrement register ifZero ifPositive) hraw
  have hfoundTape : current.foundTape =
      current.outer.moveN (orient growth .right) current.distance := by
    simp [GenuineSearch.foundTape, hdirection]
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hreverse : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (3 : Fin 5)).Matches
      ((current.outer.moveN (orient growth .right) current.distance).move
        (NestingMachine.opposite (orient growth .right)))
      (NestingMachine.opposite (orient growth .right)) distance := by
    simpa only [hfoundTape, hopposite] using hgap
  have hdistanceRaw : current.distance ≤ distance :=
    CounterControlInwardValidationReplay.reverseBoundaryGap_distance_ge
      hcurrentGap hreverse
  have hdistance : current.distance ≤ next.distance := by
    simpa [next] using hdistanceRaw
  have hprefix : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      (foundCfg next) := by
    exact hentry.trans (by
      rw [← hnextCfg]
      exact hfoundNext)
  cases outcome with
  | logical core reaches inside =>
      exact ⟨.logical core (hprefix.trans reaches)
        (hdistance.trans inside)⟩
  | nextSearch guarded reaches distance_le =>
      exact ⟨.nextSearch guarded (hprefix.trans reaches)
        (hdistance.trans distance_le)⟩

/-- The final outward validation command followed by a decrement of any
non-clock register has the instruction-wide monotone handoff required by the
validation assembly. -/
theorem outwardFour_nonclockDecrement_handoff
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : ValidationEnd current growth source
      (.decrement register ifZero ifPositive))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source
          (.decrement register ifZero ifPositive)) .preserve)
    (hregister : register ≠ .clock)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (OutwardInstructionHandoff current
      (OutwardObligation.four progress hraw)) := by
  cases register with
  | left =>
      apply outwardFour_nonemptyDecrement_handoff base c hmortal current
        growth source .left ifZero ifPositive hrule progress hraw
        (directRef growth source (bodyDirectBase + 1))
      · simp only [AnchoredCounterGeometry.routeToDecrementStart,
          routeCommandsAux, List.mem_cons]
        exact Or.inl rfl
      · simp [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
      · apply
          CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
            growth hrule
        simp [directRulesForRule, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
        exact Or.inr (Or.inl rfl)
      · exact himmortal
  | right =>
      apply outwardFour_nonemptyDecrement_handoff base c hmortal current
        growth source .right ifZero ifPositive hrule progress hraw
        (directRef growth source (bodyDirectBase + 1))
      · simp only [AnchoredCounterGeometry.routeToDecrementStart,
          routeCommandsAux, List.mem_cons]
        exact Or.inl rfl
      · simp [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
      · apply
          CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
            growth hrule
        simp [directRulesForRule, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
        exact Or.inr (Or.inl rfl)
      · exact himmortal
  | temp =>
      apply outwardFour_nonemptyDecrement_handoff base c hmortal current
        growth source .temp ifZero ifPositive hrule progress hraw
        (directRef growth source testDirectSlot)
      · simp only [AnchoredCounterGeometry.routeToDecrementStart,
          routeCommandsAux, List.mem_cons]
        exact Or.inl rfl
      · simp [bodyEntry, AnchoredCounterGeometry.routeToDecrementStart]
      · apply
          CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
            growth hrule
        simp [directRulesForRule, decrementRules,
          AnchoredCounterGeometry.routeToDecrementStart, routeEntryRules]
        exact Or.inr (Or.inl rfl)
      · exact himmortal
  | clock => exact False.elim (hregister rfl)

end

end CounterControlGenuineValidationOutwardDecrement
end Hooper
end Kari
end LeanWang
