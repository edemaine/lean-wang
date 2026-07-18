/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlDecrementEntry
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementEntry
import LeanWang.Kari.Hooper.CounterControlGuardedShiftCompletion

/-!
# Guard-free conditional-decrement entry

An arbitrary genuine caller inside `routeToDecrementStart` can complete the
preserving route without a guard, execute the decrement test, and select the
positive-shift or zero-recovery branch.  This module retains the original
route coordinates and exact branch tape, which are needed to compare the
original gap with the logical core reconstructed after either branch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineDecrementEntry

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan
open CounterControlGlobalUnnesting
open CounterControlGenuineRouteEmbedding
open CounterControlDecrementEntry
open CounterControlRouteSuffixMortality CounterControlValidationMortality
open CounterControlParentContinuation
open CounterControlGuardedDecrementEntry
open CounterControlSearchSystem
open CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlGuardedShiftCompletion
open CounterControlGuardedParentContinuation

noncomputable section

set_option maxRecDepth 10000

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- Tape after a genuine route's test rule moves into the register gap. -/
abbrev branchTape
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    FullTM0.Tape (Symbol numTags) :=
  CounterControlDecrementEntry.branchTape progress

/-- A genuine caller's shared decrement-test certificate. -/
abbrev TestHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type :=
  CounterControlDecrementEntry.TestHandoff current growth source register
    ifZero ifPositive

/-- The genuine route endpoint is centered on the tested boundary. -/
theorem decrementEntry_finish_read
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    progress.suffix.finish.read =
      boundarySymbol (MarkerSchedule.decrementStartBoundary register) :=
  CounterControlDecrementEntry.decrementEntry_finish_read progress

/-- Exact generated branch selected after the decrement test.  The route
field retained in the handoff preserves the original caller's coordinates. -/
inductive BranchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_blank : (branchTape handoff.route).read = blankSymbol)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current)
        ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)
  | zero (handoff : TestHandoff current growth source register
      ifZero ifPositive)
      (read_boundary : (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc)
      (reaches : FullTM0.Reaches
        (CounterControlNestingBridge.machine base c)
        (foundCfg current)
        ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
          (branchTape handoff.route).move (orient growth .right)⟩)

/-- Route-free branch classification.  Once the decrement test has reached
`branchDirectSlot`, immortality forces the scanned cell to carry exactly one
of the two symbols owned by this decrement rule. -/
theorem branchRead_of_reaches
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (hprogram : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hreaches : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨resolve base c (directRef growth source branchDirectSlot), T⟩)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    T.read = blankSymbol ∨ T.read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc := by
  let positiveRule : RawDirectRule :=
    ⟨growth, directRef growth source branchDirectSlot, .blank,
      searchRef growth source secondarySearchBase, .right⟩
  have hpositiveRule : positiveRule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
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
            (source, .decrement register ifZero ifPositive)
            hprogram)
      · norm_num [branchDirectSlot, directStride]
    have hsymbolic : rule.source =
        directRef growth source branchDirectSlot :=
      CounterControlDeterministic.sourceOffset_injective_on
        (CounterControlArbitraryEntry.rawDirectRule_source_wellFormed
          rule hrule) hbranchWell hoffset
    rcases CounterControlGuardedDecrementEntry.branchRule_read
        hprogram rule hrule hsymbolic with hblank | hboundary
    · left
      rw [hblank] at hmatch
      simpa [RawRead.Matches] using hmatch
    · right
      rw [hboundary] at hmatch
      simpa [RawRead.Matches] using hmatch

/-- Immortality forces the branch cell of a completed decrement-entry route
to carry exactly one symbol for which the instruction generated an outgoing
direct rule. -/
theorem branchRead_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    (branchTape handoff.route).read = blankSymbol ∨
      (branchTape handoff.route).read = boundarySymbol
        (AnchoredCounterGeometry.registerGap register).castSucc :=
  branchRead_of_reaches base c handoff.rule_mem (branchTape handoff.route)
    handoff.reaches himmortal

/-- Execute the direct rule selected by the branch-cell symbol. -/
theorem branchOutcome_of_read
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
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

/-- Complete an arbitrary genuine decrement-entry caller and select its exact
generated branch. -/
theorem branchOutcome_of_rule
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
    Nonempty (BranchOutcome current growth source register
      ifZero ifPositive) := by
  rcases testHandoff_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨handoff⟩
  exact branchOutcome_of_read base c handoff
    (branchRead_of_immortal base c handoff himmortal)

/-! ## Exact distance-zero generated branch entries -/

/-- The first positive-decrement marker shift. -/
def firstDecrementShiftRaw (growth : Turing.Dir) (source : Nat)
    (register : Register) : RawCommand :=
  .markerShift ⟨growth, source, secondarySearchBase⟩
    (MarkerSchedule.decrementStartBoundary register) .right .left
    (match register with
      | .clock => directRef growth source finishDirectSlot
      | _ => searchRef growth source (secondarySearchBase + 1))
    (some .right) none

/-- The first command in zero recovery. -/
def firstZeroRecoveryRaw (growth : Turing.Dir) (source : Nat)
    (register : Register) (ifZero : Nat) : RawCommand :=
  .boundaryNavigation ⟨growth, source, zeroSearchBase⟩
    (MarkerSchedule.decrementStartBoundary register) .right
    (match register with
      | .clock => .logical growth ifZero
      | _ => directRef growth source zeroDirectBase)
    .preserve

theorem firstDecrementShiftRaw_mem
    (growth : Turing.Dir) (source : Nat) (register : Register) :
    firstDecrementShiftRaw growth source register ∈
      decrementShiftCommands growth source register := by
  cases register <;>
    simp [firstDecrementShiftRaw, decrementShiftCommands,
      decrementShiftCommandsAux, MarkerShift.decrementOrder,
      MarkerSchedule.decrementStartBoundary]

theorem firstZeroRecoveryRaw_mem
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero : Nat) :
    firstZeroRecoveryRaw growth source register ifZero ∈
      routeCommandsAux growth source zeroSearchBase zeroDirectBase
        (.logical growth ifZero)
        (AnchoredCounterGeometry.routeFromZero register) := by
  cases register <;> exact List.mem_cons_self

theorem firstDecrementShiftRaw_mem_rawCommands
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program) :
    firstDecrementShiftRaw growth source register ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, decrementCommands,
    firstDecrementShiftRaw_mem growth source register]

theorem firstZeroRecoveryRaw_mem_rawCommands
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat)
    (hrule : (source, .decrement register ifZero ifPositive) ∈
      GlobalSourceProgram.program) :
    firstZeroRecoveryRaw growth source register ifZero ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, decrementCommands,
    firstZeroRecoveryRaw_mem growth source register ifZero]

theorem firstDecrementShiftRaw_target
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hraw : firstDecrementShiftRaw growth source register ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstDecrementShiftRaw growth source register) hraw).target =
        Target.boundary (MarkerSchedule.decrementStartBoundary register) := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstDecrementShiftRaw,
    CounterControlCommandAt.compileRawAtTag, Command.target]

theorem firstDecrementShiftRaw_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hraw : firstDecrementShiftRaw growth source register ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstDecrementShiftRaw growth source register) hraw).searchDirection =
        orient growth .right := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstDecrementShiftRaw,
    CounterControlCommandAt.compileRawAtTag, Command.searchDirection]

theorem firstZeroRecoveryRaw_target
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero : Nat)
    (hraw : firstZeroRecoveryRaw growth source register ifZero ∈
      rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstZeroRecoveryRaw growth source register ifZero) hraw).target =
        Target.boundary (MarkerSchedule.decrementStartBoundary register) := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstZeroRecoveryRaw,
    CounterControlCommandAt.compileRawAtTag, Command.target,
    compileNavigationAction]

theorem firstZeroRecoveryRaw_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero : Nat)
    (hraw : firstZeroRecoveryRaw growth source register ifZero ∈
      rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstZeroRecoveryRaw growth source register ifZero)
        hraw).searchDirection = orient growth .right := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstZeroRecoveryRaw,
    CounterControlCommandAt.compileRawAtTag, Command.searchDirection]

/-- A generated search already centered on a matching target is a genuine
search of distance zero. -/
def immediateSearch
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) : GenuineSearch base c := by
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  have hcommand : command base c search =
      CounterControlCommandAt.compileRawCommand base c raw hraw := by
    rfl
  exact {
    search := search
    outer := T
    distance := 0
    gap := by
      rw [hcommand]
      constructor
      · intro i hi
        omega
      · simpa [FullTM0.Tape.offset] using hmatch }

@[simp] theorem immediateSearch_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    (immediateSearch base c raw hraw T hmatch).cfg =
      ⟨searchState base c raw.address, T⟩ := by
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hraw
  change (searchSystem base c).startCfg search T = _
  change (⟨CounterControlSearchSystem.commandOffset base c search, T⟩ :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
  unfold CounterControlSearchSystem.commandOffset
  rw [hget]

@[simp] theorem immediateSearch_distance
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    (immediateSearch base c raw hraw T hmatch).distance = 0 :=
  rfl

theorem immediateSearch_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    (immediateSearch base c raw hraw T hmatch).direction =
      (CounterControlCommandAt.compileRawCommand base c raw hraw).searchDirection := by
  rfl

@[simp] theorem immediateSearch_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (raw : RawCommand) (hraw : raw ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hmatch : (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
      T.read) :
    (immediateSearch base c raw hraw T hmatch).selectedRaw = raw := by
  exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw

theorem branchTape_move_right
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    (progress : GenuineRouteEnd current growth source bodySearchBase
      (bodyDirectBase + 1) (directRef growth source testDirectSlot)
      (AnchoredCounterGeometry.routeToDecrementStart register)) :
    (branchTape progress).move (orient growth .right) =
      progress.suffix.finish := by
  cases growth <;>
    simp [branchTape, CounterControlDecrementEntry.branchTape,
      FullTM0.Tape.move, orient]

/-- Positive decrement reaches the first marker-shift search with exact
distance zero and a genuine blank guard behind its target. -/
structure PositiveShiftSearchHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  branch : TestHandoff current growth source register ifZero ifPositive
  read_blank : (branchTape branch.route).read = blankSymbol
  next : GuardedSearch base c
  selectedRaw_eq : next.current.selectedRaw =
    firstDecrementShiftRaw growth source register
  selectedRaw_mem : next.current.selectedRaw ∈
    decrementShiftCommands growth source register
  outer_eq : next.current.outer = branch.route.suffix.finish
  distance_eq : next.current.distance = 0
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) next.current.cfg

/-- Zero decrement reaches the first preserving recovery search with exact
distance zero.  Its predecessor is the labelled boundary detected by the
test, explaining precisely why this search need not be guarded. -/
structure ZeroRecoverySearchHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  branch : TestHandoff current growth source register ifZero ifPositive
  read_boundary : (branchTape branch.route).read = boundarySymbol
    (AnchoredCounterGeometry.registerGap register).castSucc
  next : GenuineSearch base c
  selectedRaw_eq : next.selectedRaw =
    firstZeroRecoveryRaw growth source register ifZero
  selectedRaw_mem : next.selectedRaw ∈
    routeCommandsAux growth source zeroSearchBase zeroDirectBase
      (.logical growth ifZero)
      (AnchoredCounterGeometry.routeFromZero register)
  outer_eq : next.outer = branch.route.suffix.finish
  distance_eq : next.distance = 0
  behind_boundary :
    (next.outer.move
      (NestingMachine.opposite next.direction)).read =
        boundarySymbol
          (AnchoredCounterGeometry.registerGap register).castSucc
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current) next.cfg

/-- Convert an exact positive branch into its distance-zero guarded first
shift search. -/
theorem positiveShiftSearchHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (hblank : (branchTape handoff.route).read = blankSymbol)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
        (branchTape handoff.route).move (orient growth .right)⟩) :
    Nonempty (PositiveShiftSearchHandoff current growth source register
      ifZero ifPositive) := by
  let raw := firstDecrementShiftRaw growth source register
  have hraw : raw ∈ rawCommands :=
    firstDecrementShiftRaw_mem_rawCommands growth source register ifZero
      ifPositive handoff.rule_mem
  have hmatch :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
        handoff.route.suffix.finish.read := by
    rw [firstDecrementShiftRaw_target]
    simpa [Target.Matches] using decrementEntry_finish_read handoff.route
  let genuine : GenuineSearch base c :=
    immediateSearch base c raw hraw handoff.route.suffix.finish hmatch
  have hdirection : genuine.direction = orient growth .right := by
    rw [immediateSearch_direction,
      firstDecrementShiftRaw_direction]
  let next : GuardedSearch base c := {
    current := genuine
    guard := by
      change (genuine.outer.move
        (NestingMachine.opposite genuine.direction)).read = blankSymbol
      rw [hdirection]
      have hopposite : NestingMachine.opposite (orient growth .right) =
          orient growth .left := by
        cases growth <;> rfl
      rw [hopposite]
      change (branchTape handoff.route).read = blankSymbol
      exact hblank }
  have houter := branchTape_move_right handoff.route
  have hreach' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      genuine.cfg := by
    have hrun := hreach
    rw [houter] at hrun
    rw [immediateSearch_cfg]
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨searchState base c ⟨growth, source, secondarySearchBase⟩,
        handoff.route.suffix.finish⟩
    exact hrun
  refine ⟨{
    branch := handoff
    read_blank := hblank
    next := next
    selectedRaw_eq := ?_
    selectedRaw_mem := ?_
    outer_eq := rfl
    distance_eq := rfl
    reaches := hreach' }⟩
  · exact immediateSearch_selectedRaw base c raw hraw
      handoff.route.suffix.finish hmatch
  · rw [show next.current.selectedRaw = raw by
        exact immediateSearch_selectedRaw base c raw hraw
          handoff.route.suffix.finish hmatch]
    exact firstDecrementShiftRaw_mem growth source register

/-- Convert an exact zero branch into its distance-zero first recovery
search, retaining its labelled predecessor. -/
theorem zeroRecoverySearchHandoff
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (handoff : TestHandoff current growth source register ifZero ifPositive)
    (hboundary : (branchTape handoff.route).read = boundarySymbol
      (AnchoredCounterGeometry.registerGap register).castSucc)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
        (branchTape handoff.route).move (orient growth .right)⟩) :
    Nonempty (ZeroRecoverySearchHandoff current growth source register
      ifZero ifPositive) := by
  let raw := firstZeroRecoveryRaw growth source register ifZero
  have hraw : raw ∈ rawCommands :=
    firstZeroRecoveryRaw_mem_rawCommands growth source register ifZero
      ifPositive handoff.rule_mem
  have hmatch :
      (CounterControlCommandAt.compileRawCommand base c raw hraw).target.Matches
        handoff.route.suffix.finish.read := by
    rw [firstZeroRecoveryRaw_target]
    simpa [Target.Matches] using decrementEntry_finish_read handoff.route
  let next : GenuineSearch base c :=
    immediateSearch base c raw hraw handoff.route.suffix.finish hmatch
  have hdirection : next.direction = orient growth .right := by
    rw [immediateSearch_direction,
      firstZeroRecoveryRaw_direction]
  have houter := branchTape_move_right handoff.route
  have hreach' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) (foundCfg current)
      next.cfg := by
    have hrun := hreach
    rw [houter] at hrun
    rw [immediateSearch_cfg]
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current)
      ⟨searchState base c ⟨growth, source, zeroSearchBase⟩,
        handoff.route.suffix.finish⟩
    exact hrun
  refine ⟨{
    branch := handoff
    read_boundary := hboundary
    next := next
    selectedRaw_eq := ?_
    selectedRaw_mem := ?_
    outer_eq := rfl
    distance_eq := rfl
    behind_boundary := ?_
    reaches := hreach' }⟩
  · exact immediateSearch_selectedRaw base c raw hraw
      handoff.route.suffix.finish hmatch
  · rw [show next.selectedRaw = raw by
        exact immediateSearch_selectedRaw base c raw hraw
          handoff.route.suffix.finish hmatch]
    exact firstZeroRecoveryRaw_mem growth source register ifZero
  · rw [hdirection]
    have hopposite : NestingMachine.opposite (orient growth .right) =
        orient growth .left := by
      cases growth <;> rfl
    rw [hopposite]
    exact hboundary

/-- Fully packaged generated-search endpoint of either decrement branch. -/
inductive BranchSearchOutcome
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  | positive (handoff : PositiveShiftSearchHandoff current growth source
      register ifZero ifPositive)
  | zero (handoff : ZeroRecoverySearchHandoff current growth source register
      ifZero ifPositive)

/-- Package either exact direct branch as its first generated search. -/
theorem branchSearchOutcome
    (base : Nat) (c : Nat.Partrec.Code)
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (outcome : BranchOutcome current growth source register
      ifZero ifPositive) :
    Nonempty (BranchSearchOutcome current growth source register
      ifZero ifPositive) := by
  cases outcome with
  | positive handoff hblank hreach =>
      rcases positiveShiftSearchHandoff base c handoff hblank hreach with
        ⟨next⟩
      exact ⟨BranchSearchOutcome.positive next⟩
  | zero handoff hboundary hreach =>
      rcases zeroRecoverySearchHandoff base c handoff hboundary hreach with
        ⟨next⟩
      exact ⟨BranchSearchOutcome.zero next⟩

/-- Complete and package an arbitrary genuine decrement-entry caller through
the route, test, branch, and first generated branch search. -/
theorem branchSearchOutcome_of_rule
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
    Nonempty (BranchSearchOutcome current growth source register
      ifZero ifPositive) := by
  rcases branchOutcome_of_rule base c hmortal current himmortal growth source
      register ifZero ifPositive hrule hcommand with ⟨outcome⟩
  exact branchSearchOutcome base c outcome

/-! ## Continuing the packaged branch searches -/

/-- The guarded positive entry advances through the complete remaining
marker-shift schedule. -/
theorem PositiveShiftSearchHandoff.shiftSuffix_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : PositiveShiftSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (DecrementShiftSuffixReached entry.next growth source
      register) := by
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) entry.next.current.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal entry.reaches
  have himmortalFound := immortalFrom_foundCfg entry.next.current
    himmortalNext
  exact decrementShift_suffix_of_immortal base c hmortal entry.next growth
    source register ifZero ifPositive entry.branch.rule_mem
    entry.selectedRaw_mem himmortalFound

/-- Fully discharged positive-decrement direct endpoint, retaining the
original decrement-entry route through `entry`. -/
structure PositiveLogicalHandoff
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (ifZero ifPositive : Nat) : Type where
  entry : PositiveShiftSearchHandoff current growth source register
    ifZero ifPositive
  direct : DecrementPositiveDirectHandoff entry.next growth source register
    ifZero ifPositive
  reaches : FullTM0.Reaches (CounterControlNestingBridge.machine base c)
    (foundCfg current)
    ⟨logicalState base c growth ifPositive,
      decrementPositiveTape direct.suffix⟩

/-- Run the positive branch through all marker shifts and final direct glue
to bounded logical control. -/
theorem PositiveShiftSearchHandoff.logicalHandoff_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : PositiveShiftSearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (PositiveLogicalHandoff current growth source register
      ifZero ifPositive) := by
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) entry.next.current.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal entry.reaches
  have hfound := reaches_foundCfg_of_immortal entry.next.current
    himmortalNext
  rcases entry.shiftSuffix_of_immortal hmortal himmortal with ⟨suffix⟩
  rcases decrementPositiveDirectHandoff base c entry.next growth source
      register ifZero ifPositive entry.branch.rule_mem suffix with
    ⟨direct⟩
  exact ⟨⟨entry, direct,
    entry.reaches.trans (hfound.trans direct.reaches)⟩⟩

/-- The zero branch feeds directly into the guard-free recovery-route
embedding.  The outcome is indexed by the distance-zero recovery search;
the original route retained in `entry` supplies the stronger comparison
needed when assembling an outcome for `current`. -/
theorem ZeroRecoverySearchHandoff.monotoneOutcome_of_immortal
    {base : Nat} {c : Nat.Partrec.Code}
    {current : GenuineSearch base c}
    {growth : Turing.Dir} {source : Nat} {register : Register}
    {ifZero ifPositive : Nat}
    (entry : ZeroRecoverySearchHandoff current growth source register
      ifZero ifPositive)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    Nonempty (FoundMonotoneGuardedEntryOutcome entry.next) := by
  have himmortalNext : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) entry.next.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal entry.reaches
  have himmortalFound := immortalFrom_foundCfg entry.next himmortalNext
  exact CounterControlGenuineRouteEmbedding.zeroRecovery_logical_of_rule
    base c hmortal entry.next himmortalFound growth source register ifZero
      ifPositive entry.branch.rule_mem entry.selectedRaw_mem

end

end CounterControlGenuineDecrementEntry
end Hooper
end Kari
end LeanWang
