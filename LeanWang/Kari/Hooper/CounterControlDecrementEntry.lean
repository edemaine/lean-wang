/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Conditional-decrement route handoff

This module contains the proof-neutral part of conditional-decrement entry.
It completes a genuine preserving-route endpoint with the decrement test.
Guarded and guard-free callers share this certificate and differ only in how
they obtain the route endpoint and use the subsequent branch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlDecrementEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlGenuineRouteEmbedding
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## The final target of a retained route suffix -/

/-- Last target of a route suffix, including the already found current leg. -/
def lastRouteTarget (current : MarkerValidation.Leg)
    (remaining : List MarkerValidation.Leg) : Fin 5 :=
  ((current :: remaining).getLast (by simp)).target

@[simp] theorem lastRouteTarget_nil (current : MarkerValidation.Leg) :
    lastRouteTarget current [] = current.target := by
  rfl

/-- A complete nonempty route trace finishes on its final labelled target. -/
theorem routeGaps_finish_read
    {growth : Turing.Dir} {route : List MarkerValidation.Leg}
    {outer finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteGaps growth route outer finish)
    (hne : route ≠ []) :
    finish.read = boundarySymbol ((route.getLast hne).target) := by
  induction trace with
  | last leg outer distance gap =>
      have hmarked := gap.marked
      change outer (FullTM0.Tape.offset
        (orient growth leg.direction) distance) =
          boundarySymbol leg.target at hmarked
      simpa [FullTM0.Tape.read_moveN] using hmarked
  | cons leg next rest outer distance gap finish tail ih =>
      simpa using ih (by simp)

/-- Starting at the already found current leg, a route tail finishes on the
last target of `current :: remaining`. -/
theorem routeTailGaps_finish_read
    {growth : Turing.Dir} {remaining : List MarkerValidation.Leg}
    {start finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteTailGaps growth remaining start finish)
    (current : MarkerValidation.Leg)
    (hcurrent : start.read = boundarySymbol current.target) :
    finish.read = boundarySymbol (lastRouteTarget current remaining) := by
  cases trace with
  | nil => simpa using hcurrent
  | cons next rest start finish tail =>
      simpa [lastRouteTarget] using routeGaps_finish_read tail (by simp)

/-- The final leg of a nonempty decrement-entry route targets the boundary
immediately after the selected register. -/
theorem decrementEntry_lastTarget
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    lastRouteTarget progress.suffix.current progress.suffix.remaining =
      MarkerSchedule.decrementStartBoundary register := by
  cases register with
  | clock =>
      have himpossible := progress.suffix.route_eq
      simp [AnchoredCounterGeometry.routeToDecrementStart] at himpossible
  | left =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 1 at htarget
      exact htarget
  | right =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 2 at htarget
      exact htarget
  | temp =>
      have hlast := congrArg List.getLast? progress.suffix.route_eq
      rw [List.getLast?_append_cons,
        List.getLast?_eq_some_getLast (by
          simp [AnchoredCounterGeometry.routeToDecrementStart]),
        List.getLast?_eq_some_getLast (by simp)] at hlast
      have htarget := congrArg MarkerValidation.Leg.target
        (Option.some.inj hlast).symm
      change lastRouteTarget progress.suffix.current
        progress.suffix.remaining = 3 at htarget
      exact htarget

/-- The completed route is centered on the boundary tested by the decrement
instruction. -/
theorem decrementEntry_finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    progress.suffix.finish.read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) := by
  have hread := routeTailGaps_finish_read progress.suffix.tailGaps
    progress.suffix.current progress.current_read
  rw [decrementEntry_lastTarget progress] at hread
  exact hread

/-! ## Exact test handoff -/

/-- Tape after the test rule moves left into the selected register gap. -/
def branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    FullTM0.Tape (Symbol numTags) :=
  progress.suffix.finish.move (orient growth .left)

/-- Exact completion of a decrement-entry route and its test rule. -/
structure TestHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  rule_mem : (source, .decrement register ifZero ifPositive) ∈
    GlobalSourceProgram.program
  route : GenuineRouteEnd current growth source bodySearchBase
    (bodyDirectBase + 1) (directRef growth source testDirectSlot)
    (AnchoredCounterGeometry.routeToDecrementStart register)
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    ⟨resolve base c (directRef growth source branchDirectSlot),
      branchTape route⟩

/-- Execute the exact boundary test after a completed decrement-entry route. -/
theorem testHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  let raw : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot,
      .boundary (MarkerSchedule.decrementStartBoundary register),
      directRef growth source branchDirectSlot, .left⟩
  have hraw : raw ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change raw ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [raw, decrementRules]
  have hmatch : raw.read.Matches progress.suffix.finish.read := by
    simpa [raw, RawRead.Matches] using decrementEntry_finish_read progress
  have htest := CounterControlDirectSemantics.reaches_directRule base c raw
    hraw progress.suffix.finish hmatch
  have htest' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        progress.suffix.finish⟩
      ⟨resolve base c (directRef growth source branchDirectSlot),
        branchTape progress⟩ := by
    change FullTM0.Reaches (FiniteTM0.machine
      (CounterControlPlan.table base c)) _ _
    simpa [raw, branchTape] using htest
  exact ⟨⟨hrule, progress, progress.reaches.trans htest'⟩⟩

/-- Complete a selected decrement-entry route and execute its boundary test. -/
theorem testHandoff_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  have hcommands : ∀ command,
      command ∈ routeCommandsAux growth source bodySearchBase
          (bodyDirectBase + 1) (directRef growth source testDirectSlot)
          (AnchoredCounterGeometry.routeToDecrementStart register) →
        command ∈ rawCommands := by
    intro command hmem
    exact CounterControlPlan.command_mem_rawCommands_of_rule
      growth hrule (by simp [commandsForRule, decrementCommands, hmem])
  have hcontinuations : ∀ rule,
      rule ∈ routeContinuationRules growth source bodySearchBase
          (bodyDirectBase + 1)
          (AnchoredCounterGeometry.routeToDecrementStart register) →
        rule ∈ rawDirectRules := by
    intro rule hmem
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    simp [directRulesForRule, decrementRules, hmem]
  rcases progressedRoute base c hmortal current himmortal growth source
      bodySearchBase (bodyDirectBase + 1)
      (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register) hcommand
      hcommands hcontinuations with ⟨progress⟩
  exact testHandoff base c current growth source register ifZero ifPositive
    hrule progress

/-! ## Representation-independent branch selection -/

/-- The only generated rules owned by a decrement branch source read the
positive-case blank or that register's preceding boundary. -/
theorem branchRule_read
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (hprogram : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (hsource : rule.source = directRef growth source branchDirectSlot) :
    rule.read = .blank ∨
      rule.read = .boundary
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  obtain ⟨symbol, hsymbol⟩ : ∃ symbol, symbol ∈ symbolsForRead rule.read := by
    cases rule.read with
    | blank => exact ⟨blankSymbol, by simp [symbolsForRead]⟩
    | boundary label =>
        exact ⟨boundarySymbol label, by simp [symbolsForRead]⟩
    | nonblank =>
        exact ⟨boundarySymbol ⟨0, by decide⟩, by
          simp [symbolsForRead, nonblankSymbols]⟩
  rcases (mem_rawDirectRules_iff rule).1 hrule with
    ⟨orientation, programRule, hprogramRule, hlocal⟩
  have hkey : (rule.source, symbol) ∈
      CounterControlDeterministic.rawDirectControlKeysForRule
        orientation programRule :=
    CounterControlDeterministic.mem_rawDirectControlKeysForRule
      orientation programRule rule hlocal symbol hsymbol
  have howns :=
    CounterControlDeterministic.rawDirectControlKeysForRule_owns
      orientation programRule (rule.source, symbol) hkey
  rw [hsource] at howns
  change growth = orientation ∧ source = programRule.1 at howns
  rcases programRule with ⟨programSource, instruction⟩
  have hgrowth := howns.1
  have hprogramSource := howns.2
  change source = programSource at hprogramSource
  subst growth
  subst programSource
  have hlookupRule :=
    (CounterProgram.lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hprogramRule
  have hlookupExpected :=
    (CounterProgram.lookupInstruction_eq_some_iff_of_deterministic
      GlobalSourceProgram.program_deterministic).2 hprogram
  rw [hlookupExpected] at hlookupRule
  have hinstruction := Option.some.inj hlookupRule
  subst instruction
  clear howns hkey hsymbol hprogramRule hlookupRule hlookupExpected hprogram
  cases register <;>
    simp_all [directRulesForRule, validationRules, decrementRules,
      routeEntryRules, routeContinuationRules,
      routeContinuationRulesFrom, MarkerValidation.sweep,
      AnchoredCounterGeometry.routeToDecrementStart,
      AnchoredCounterGeometry.routeFromZero, directRef,
      MarkerSchedule.decrementStartBoundary,
      AnchoredCounterGeometry.registerGap] <;>
    norm_num [validationDirectBase, bodyDirectBase, testDirectSlot,
      branchDirectSlot, finishDirectSlot, zeroDirectBase] at * <;>
    aesop

/-- Once an immortal execution reaches a decrement branch source, its tape
symbol must select one of the two rules owned by that source. -/
theorem branchRead_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (hprogram : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State)
    (T : FullTM0.Tape (Symbol numTags))
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨resolve base c (directRef growth source branchDirectSlot), T⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start) :
    T.read = blankSymbol ∨ T.read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  let positiveRule : RawDirectRule :=
    ⟨growth, directRef growth source branchDirectSlot, .blank,
      searchRef growth source secondarySearchBase, .right⟩
  have hpositiveRule : positiveRule ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hprogram
    change positiveRule ∈ validationRules growth source ++
      decrementRules growth source register ifZero ifPositive
    apply List.mem_append_right
    simp [positiveRule, decrementRules]
  have hsourceDirect :
      resolve base c (directRef growth source branchDirectSlot) ∈
        FiniteTM0.sourceStates (directTable base c) := by
    simp only [directTable, FiniteTM0.sourceStates, List.map_flatMap,
      List.mem_flatMap]
    refine ⟨positiveRule, hpositiveRule, ?_⟩
    simp only [directRuleTable, List.map_map, List.mem_map,
      FiniteTM0.Rule.mk, Function.comp_apply]
    refine ⟨blankSymbol, ?_, ?_⟩
    · simp [positiveRule, symbolsForRead]
    · simp [positiveRule]
  have himmortalBranch := FullTM0.ImmortalFrom.of_reaches himmortal hreaches
  rcases CounterControlArbitraryEntry.direct_step_or_haltsFrom base c
      (resolve base c (directRef growth source branchDirectSlot))
      T hsourceDirect with
    hhalts | ⟨rule, hrule, hnumeric, hmatch, _hstep⟩
  · exact False.elim
      ((FullTM0.HaltsFrom.immortalFrom_iff_not _ _).mp
        himmortalBranch hhalts)
  · have hruleCounter :
        CounterControlDeterministic.IsCounterSource rule.source :=
      CounterControlDeterministic.rawDirectRules_counter_sources rule hrule
    have hbranchCounter : CounterControlDeterministic.IsCounterSource
        (directRef growth source branchDirectSlot) := by
      simp [directRef, CounterControlDeterministic.IsCounterSource]
    have hoffset : CounterControlDeterministic.sourceOffset rule.source =
        CounterControlDeterministic.sourceOffset
          (directRef growth source branchDirectSlot) := by
      apply Nat.add_left_cancel
      calc
        rightLogicalBase base c +
              CounterControlDeterministic.sourceOffset rule.source =
            resolve base c rule.source :=
          (CounterControlDeterministic.resolve_eq_add_sourceOffset
            base c hruleCounter).symm
        _ = resolve base c
              (directRef growth source branchDirectSlot) := hnumeric.symm
        _ = rightLogicalBase base c +
              CounterControlDeterministic.sourceOffset
                (directRef growth source branchDirectSlot) :=
          CounterControlDeterministic.resolve_eq_add_sourceOffset
            base c hbranchCounter
    have hbranchWell : CounterControlDeterministic.WellFormedSource
        (directRef growth source branchDirectSlot) := by
      change source < logicalSpan ∧ branchDirectSlot < directStride
      constructor
      · exact state_lt_logicalSpan
          (source_mem_programStates
            (source, .decrement register ifZero ifPositive) hprogram)
      · norm_num [branchDirectSlot, directStride]
    have hsymbolic : rule.source =
        directRef growth source branchDirectSlot :=
      CounterControlDeterministic.sourceOffset_injective_on
        (CounterControlArbitraryEntry.rawDirectRule_source_wellFormed
          rule hrule) hbranchWell hoffset
    rcases branchRule_read hprogram rule hrule hsymbolic with
      hblank | hboundary
    · left
      rw [hblank] at hmatch
      simpa [RawRead.Matches] using hmatch
    · right
      rw [hboundary] at hmatch
      simpa [RawRead.Matches] using hmatch

/-- The single direct step selected at a decrement branch source. -/
inductive BranchStep
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (T : FullTM0.Tape (Symbol numTags)) : Type where
  | positive
      (read_blank : T.read = blankSymbol)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot), T⟩
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          T.move (orient growth .right)⟩)
  | zero
      (read_boundary : T.read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot), T⟩
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          T.move (orient growth .right)⟩)

/-- Execute the generated direct rule selected by a classified branch-cell
symbol. -/
theorem branchStep_of_read
    (base : Nat) (c : Nat.Partrec.Code)
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (hprogram : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = blankSymbol ∨
      T.read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc) :
    Nonempty (BranchStep base c growth source register T) := by
  rcases hread with hblank | hboundary
  · let raw : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot, .blank,
        searchRef growth source secondarySearchBase, .right⟩
    have hraw : raw ∈ rawDirectRules := by
      apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
        growth hprogram
      change raw ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [raw, decrementRules]
    have hmatch : raw.read.Matches T.read := by
      simpa [raw, RawRead.Matches] using hblank
    have hstep := CounterControlDirectSemantics.reaches_directRule base c raw
      hraw T hmatch
    refine ⟨BranchStep.positive hblank ?_⟩
    change FullTM0.Reaches (FiniteTM0.machine
      (CounterControlPlan.table base c)) _ _
    simpa [raw, searchRef, resolve] using hstep
  · let raw : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot,
        .boundary (AnchoredCounterGeometry.registerGap register).castSucc,
        searchRef growth source zeroSearchBase, .right⟩
    have hraw : raw ∈ rawDirectRules := by
      apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
        growth hprogram
      change raw ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [raw, decrementRules]
    have hmatch : raw.read.Matches T.read := by
      simpa [raw, RawRead.Matches] using hboundary
    have hstep := CounterControlDirectSemantics.reaches_directRule base c raw
      hraw T hmatch
    refine ⟨BranchStep.zero hboundary ?_⟩
    change FullTM0.Reaches (FiniteTM0.machine
      (CounterControlPlan.table base c)) _ _
    simpa [raw, searchRef, resolve] using hstep

end

end CounterControlDecrementEntry
end Hooper
end Kari
end LeanWang
