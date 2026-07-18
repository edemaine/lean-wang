/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedRouteEmbedding
import LeanWang.Kari.Hooper.CounterControlDecrementEntry
import LeanWang.Kari.Hooper.CounterControlArbitraryEntry

/-!
# Guarded conditional-decrement entry

A generated caller inside `routeToDecrementStart` first completes that
preserving route, then executes the decrement test and its two-way direct
branch.  This file retains the exact endpoint tape.  On an immortal orbit,
the branch cell is forced to be either blank, entering the positive shift
schedule, or the preceding labelled boundary, entering zero recovery.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedDecrementEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting CounterControlGuardedSearch
open CounterControlGuardedRouteEmbedding
open CounterControlDecrementEntry
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlParentContinuation

noncomputable section

set_option maxRecDepth 10000

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-! ## Shared route and test handoff -/

/-- Compatibility wrapper for the shared route endpoint read theorem. -/
theorem routeGaps_finish_read
    {growth : Turing.Dir} {route : List MarkerValidation.Leg}
    {outer finish : FullTM0.Tape (Symbol numTags)}
    (trace : RouteGaps growth route outer finish)
    (hne : route ≠ []) :
    finish.read = boundarySymbol ((route.getLast hne).target) :=
  CounterControlDecrementEntry.routeGaps_finish_read trace hne

/-- Tape after a guarded route's test rule moves into the register gap. -/
abbrev branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GuardedRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    FullTM0.Tape (Symbol numTags) :=
  CounterControlDecrementEntry.branchTape progress

/-- A guarded caller's shared decrement-test certificate. -/
abbrev TestHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type :=
  CounterControlDecrementEntry.TestHandoff current.current growth source
    register ifZero ifPositive

/-- The guarded route endpoint is centered on the tested boundary. -/
theorem decrementEntry_finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GuardedRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    progress.suffix.finish.read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) :=
  CounterControlDecrementEntry.decrementEntry_finish_read progress

/-- Complete a guarded decrement-entry route and execute its boundary test. -/
theorem testHandoff_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (TestHandoff current growth source register ifZero ifPositive) := by
  exact CounterControlDecrementEntry.testHandoff_of_rule base c hmortal
    current.current himmortal growth source register ifZero ifPositive hrule
    hcommand

/-- The only generated rules owned by a particular decrement branch source
read either the positive-case blank or that register's preceding boundary. -/
theorem branchRule_read
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (hprogram : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (rule : RawDirectRule) (hrule : rule ∈ rawDirectRules)
    (hsource : rule.source =
      directRef growth source branchDirectSlot) :
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

/-- Exact branch selected after the decrement test. -/
inductive BranchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_blank : (branchTape handoff.route).read = blankSymbol)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)
  | zero (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_boundary : (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current.current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)

/-- Immortality forces the decrement branch cell to carry exactly one of
the two symbols for which this instruction generated an outgoing rule. -/
theorem branchRead_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    (branchTape handoff.route).read = blankSymbol ∨
      (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  let positiveRule : RawDirectRule :=
    ⟨growth, directRef growth source branchDirectSlot, .blank,
      searchRef growth source secondarySearchBase, .right⟩
  have hpositiveRule : positiveRule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth handoff.rule_mem
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
  have himmortalBranch := FullTM0.ImmortalFrom.of_reaches himmortal
    handoff.reaches
  rcases CounterControlArbitraryEntry.direct_step_or_haltsFrom base c
      (resolve base c (directRef growth source branchDirectSlot))
      (branchTape handoff.route) hsourceDirect with
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
            (source, .decrement register ifZero ifPositive)
            handoff.rule_mem)
      · norm_num [branchDirectSlot, directStride]
    have hsymbolic : rule.source =
        directRef growth source branchDirectSlot :=
      CounterControlDeterministic.sourceOffset_injective_on
        (CounterControlArbitraryEntry.rawDirectRule_source_wellFormed
          rule hrule) hbranchWell hoffset
    rcases branchRule_read handoff.rule_mem rule hrule hsymbolic with
      hblank | hboundary
    · left
      rw [hblank] at hmatch
      simpa [RawRead.Matches] using hmatch
    · right
      rw [hboundary] at hmatch
      simpa [RawRead.Matches] using hmatch

/-- Given the symbol selected at the branch cell, execute the corresponding
generated direct rule to the first positive-shift or zero-recovery search. -/
theorem branchOutcome_of_read
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GuardedSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (hread : (branchTape handoff.route).read = blankSymbol ∨
      (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc) :
    Nonempty (BranchOutcome current growth source register
      ifZero ifPositive) := by
  rcases hread with hblank | hboundary
  · let raw : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot, .blank,
        searchRef growth source secondarySearchBase, .right⟩
    have hraw : raw ∈ rawDirectRules := by
      apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
        growth handoff.rule_mem
      change raw ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [raw, decrementRules]
    have hmatch : raw.read.Matches (branchTape handoff.route).read := by
      simpa [raw, RawRead.Matches] using hblank
    have hstep := CounterControlDirectSemantics.reaches_directRule base c raw
      hraw (branchTape handoff.route) hmatch
    refine ⟨BranchOutcome.positive handoff hblank ?_⟩
    have hstep' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          branchTape handoff.route⟩
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩ := by
      change FullTM0.Reaches (FiniteTM0.machine
        (CounterControlPlan.table base c)) _ _
      simpa [raw, searchRef, resolve] using hstep
    exact handoff.reaches.trans hstep'
  · let raw : RawDirectRule :=
      ⟨growth, directRef growth source branchDirectSlot,
        .boundary (AnchoredCounterGeometry.registerGap register).castSucc,
        searchRef growth source zeroSearchBase, .right⟩
    have hraw : raw ∈ rawDirectRules := by
      apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
        growth handoff.rule_mem
      change raw ∈ validationRules growth source ++
        decrementRules growth source register ifZero ifPositive
      apply List.mem_append_right
      simp [raw, decrementRules]
    have hmatch : raw.read.Matches (branchTape handoff.route).read := by
      simpa [raw, RawRead.Matches] using hboundary
    have hstep := CounterControlDirectSemantics.reaches_directRule base c raw
      hraw (branchTape handoff.route) hmatch
    refine ⟨BranchOutcome.zero handoff hboundary ?_⟩
    have hstep' : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        ⟨resolve base c (directRef growth source branchDirectSlot),
          branchTape handoff.route⟩
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩ := by
      change FullTM0.Reaches (FiniteTM0.machine
        (CounterControlPlan.table base c)) _ _
      simpa [raw, searchRef, resolve] using hstep
    exact handoff.reaches.trans hstep'

/-- Complete a guarded decrement-entry caller and select its exact generated
branch.  Immortality excludes every disabled branch symbol. -/
theorem branchOutcome_of_rule
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      routeCommandsAux growth source bodySearchBase (bodyDirectBase + 1)
        (directRef growth source testDirectSlot)
        (AnchoredCounterGeometry.routeToDecrementStart register)) :
    Nonempty (BranchOutcome current growth source register
      ifZero ifPositive) := by
  rcases testHandoff_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨handoff⟩
  exact branchOutcome_of_read base c handoff
    (branchRead_of_immortal base c handoff himmortal)

end

end CounterControlGuardedDecrementEntry
end Hooper
end Kari
end LeanWang
