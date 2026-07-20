/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedCoordinates
import LeanWang.Kari.Hooper.CounterControlGuardedParentContinuation
import LeanWang.Kari.Hooper.CounterControlGeneratedSearchGap
import LeanWang.Kari.Hooper.CounterControlValidationMortality
import LeanWang.Kari.Hooper.CounterControlRouteRoundtrip

/-!
# Replaying an inward validation search outwards

An inward command in the symmetric validation sweep is followed, after the
smaller nested validation cycle, by an outward command which starts just
beyond the boundary found by the original command.  This file stops the
operational validation trace at that generated search entry.  The erased
guard behind the original generated search then proves that the replay gap
is strictly longer.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlInwardValidationReplay

open Turing CounterMachine
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlValidationMortality
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedSearch
open CounterControlCommandContinuationMortality
open CounterControlExactCommandContinuation
open CounterControlRouteRoundtrip

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

private abbrev validationCommand_mem :=
  CounterControlPlan.validationCommand_mem_rawCommands

private abbrev validationRule_mem :=
  CounterControlPlan.validationRule_mem_rawDirectRules

/-- Take the direct one-cell continuation after a validation command whose
target has already been found. -/
private theorem reaches_validationNext_entry
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (slot : Nat) (expected : Fin 5) (nextDirection : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol expected)
    (hvalidation : RawDirectRule.mk growth
      (directRef growth source slot) (.boundary expected)
      (searchRef growth source (slot + 1)) nextDirection ∈
        validationRules growth source)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨resolve base c (directRef growth source slot), T⟩) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c ⟨growth, source, slot + 1⟩,
        T.move (orient growth nextDirection)⟩ := by
  let rule : RawDirectRule :=
    ⟨growth, directRef growth source slot, .boundary expected,
      searchRef growth source (slot + 1), nextDirection⟩
  have hruleGlobal : rule ∈ rawDirectRules := by
    apply validationRule_mem growth source instruction hrule
    simpa [rule] using hvalidation
  have hmatch : rule.read.Matches T.read := by
    simpa [rule, RawRead.Matches] using hread
  have hlocal := CounterControlDirectSemantics.reaches_directRule
    base c rule hruleGlobal T hmatch
  have hlocal' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source slot), T⟩
      ⟨searchState base c ⟨growth, source, slot + 1⟩,
        T.move (orient growth nextDirection)⟩ := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table, rule,
      searchRef, CounterControlPlan.resolve] using hlocal
  exact hreach.trans hlocal'

/-- Resolve one intermediate preserving validation search and take its
direct continuation to the following validation search. -/
private theorem reaches_validationNext_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (slot : Nat) (expected : Fin 5) (direction : Turing.Dir)
    (nextDirection : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags))
    (hcommandValidation : RawCommand.boundaryNavigation
      ⟨growth, source, slot⟩ expected direction
      (directRef growth source slot) .preserve ∈
        validationCommands growth source instruction)
    (hruleValidation : RawDirectRule.mk growth
      (directRef growth source slot) (.boundary expected)
      (searchRef growth source (slot + 1)) nextDirection ∈
        validationRules growth source)
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c ⟨growth, source, slot⟩, outer⟩) :
    ∃ distance,
      SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary expected).Matches outer
          (orient growth direction) distance ∧
        FullTM0.Reaches (CounterControlNestingBridge.machine base c) start
          ⟨searchState base c ⟨growth, source, slot + 1⟩,
            (outer.moveN (orient growth direction) distance).move
              (orient growth nextDirection)⟩ := by
  have hraw := validationCommand_mem growth source instruction hrule
    hcommandValidation
  have hcontinuation := validationRule_mem growth source instruction hrule
    hruleValidation
  exact CounterControlArbitraryMortality.reaches_nextSearch_of_immortal_boundary_preserve
    base c hmortal himmortal ⟨growth, source, slot⟩ expected direction
    (directRef growth source slot) ⟨growth, source, slot + 1⟩
    nextDirection hraw hcontinuation outer hreach

private theorem moveN_move_moveN_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance reverseDistance : Nat) (hreverse : reverseDistance < distance) :
    ((T.moveN direction distance).move
        (NestingMachine.opposite direction)).moveN
          (NestingMachine.opposite direction) reverseDistance =
      T.moveN direction (distance - (reverseDistance + 1)) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move] <;>
    congr 1 <;> omega

/-- A boundary search starting immediately beyond the found end of a blank
gap must travel at least as far as that gap before finding any boundary in
the reverse direction. -/
theorem reverseBoundaryGap_distance_ge
    {outer : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance replayDistance : Nat} {target replayTarget : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches outer direction distance)
    (hreplay : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary replayTarget).Matches
      ((outer.moveN direction distance).move
        (NestingMachine.opposite direction))
      (NestingMachine.opposite direction) replayDistance) :
    distance ≤ replayDistance := by
  by_contra hnot
  have hlt : replayDistance < distance := by omega
  let index := distance - (replayDistance + 1)
  have hindex : index < distance := by
    dsimp [index]
    omega
  have hblank := hgap.blank hindex
  have hmarked := hreplay.marked
  have htapes := moveN_move_moveN_opposite outer direction distance
    replayDistance hlt
  have hread :
      (((outer.moveN direction distance).move
          (NestingMachine.opposite direction)).moveN
            (NestingMachine.opposite direction) replayDistance).read =
        outer (FullTM0.Tape.offset direction index) := by
    rw [htapes]
    simp [index]
  have hboundary :
      outer (FullTM0.Tape.offset direction index) =
        boundarySymbol replayTarget := by
    rw [← hread]
    simpa [FullTM0.Tape.read_moveN, Target.Matches] using hmarked
  rw [hboundary] at hblank
  exact blankSymbol_ne_boundarySymbol replayTarget hblank.symm

private theorem selectedRaw_right_false
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source slot : Nat) (expected : Fin 5)
    (success : ControlRef)
    (hdirection : current.direction = orient growth .left)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, slot⟩ expected .right success .preserve) : False := by
  have hphysical := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hphysical
  rw [hraw, hdirection] at hphysical
  cases growth <;> contradiction

private theorem foundTape_read_of_selectedRaw_boundary
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation address expected
      direction success .preserve) :
    current.foundTape.read = boundarySymbol expected := by
  have hmatch := current.selectedRaw_target_matches_foundTape
  simpa [CounterControlCommandAt.compileRawAtTag,
    CounterControlCommandAt.compileRawCommand_spec, hraw,
    compileNavigationAction, Command.target, Target.Matches] using hmatch

private theorem parentGap_of_selectedRaw_boundary
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : current.selectedRaw = .boundaryNavigation address expected
      direction success .preserve) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches current.parentOuter
      (orient address.growth direction) (current.current.distance + 1) := by
  have hgap := current.parentGap
  rw [← current.compileRawCommand_selectedRaw] at hgap
  have hdirection := current.selectedRaw_direction_eq
  have hdirection' : orient address.growth direction = current.direction := by
    simpa [CounterControlCommandAt.compileRawAtTag,
      CounterControlCommandAt.compileRawCommand_spec, hraw,
      compileNavigationAction, Command.searchDirection] using hdirection
  rw [hdirection']
  simpa [CounterControlCommandAt.compileRawAtTag,
    CounterControlCommandAt.compileRawCommand_spec, hraw,
    compileNavigationAction, Command.target] using hgap

private theorem selectedRaw_inward_cases
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (hdirection : current.direction = orient growth .left) :
    current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 0⟩ 3 .left (directRef growth source 0)
          .preserve ∨
      current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 1⟩ 2 .left (directRef growth source 1)
          .preserve ∨
      current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 2⟩ 1 .left (directRef growth source 2)
          .preserve ∨
      current.selectedRaw = .boundaryNavigation
        ⟨growth, source, 3⟩ 0 .left (directRef growth source 3)
          .preserve := by
  simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
    validationSearchBase, validationDirectBase] at hcommand
  rcases hcommand with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr h3))
  · exact (selectedRaw_right_false current growth source 4 1
      (directRef growth source 4) hdirection h4).elim
  · exact (selectedRaw_right_false current growth source 5 2
      (directRef growth source 5) hdirection h5).elim
  · exact (selectedRaw_right_false current growth source 6 3
      (directRef growth source 6) hdirection h6).elim
  · exact (selectedRaw_right_false current growth source 7 4
      (bodyEntry growth source instruction) hdirection h7).elim

/-- Package a reached generated boundary-navigation entry together with the
finite gap forced by immortality. -/
private theorem reachedBoundarySearch_of_immortal
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) start)
    (address : SearchAddress) (expected : Fin 5)
    (direction : Turing.Dir) (success : ControlRef)
    (hraw : RawCommand.boundaryNavigation address expected direction success
      .preserve ∈ rawCommands)
    (outer : FullTM0.Tape (Symbol numTags))
    (hreach : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) start
      ⟨searchState base c address, outer⟩) :
    ∃ replay : ReachedGenuineSearch base c start,
      replay.search = CounterControlCommandAt.rawTag
        (.boundaryNavigation address expected direction success .preserve)
        hraw ∧
      replay.outer = outer := by
  let raw : RawCommand :=
    .boundaryNavigation address expected direction success .preserve
  have himmortalEntry := FullTM0.ImmortalFrom.of_reaches himmortal hreach
  rcases CounterControlGeneratedSearchGap.boundaryNavigation_gap_of_immortal
      base c hmortal address expected direction success .preserve hraw outer
      himmortalEntry with ⟨distance, hgap⟩
  let search : Search := CounterControlCommandAt.rawTag raw hraw
  have hcommand : command base c search =
      CounterControlCommandAt.compileRawCommand base c raw hraw := by
    rfl
  have hgap' : SearchGap (fun symbol => symbol = blankSymbol)
      (command base c search).target.Matches outer
      (command base c search).searchDirection distance := by
    rw [hcommand, CounterControlCommandAt.compileRawCommand_spec]
    simpa [raw, CounterControlCommandAt.compileRawAtTag,
      compileNavigationAction, Command.target, Command.searchDirection]
      using hgap
  let genuine : GenuineSearch base c := ⟨search, outer, distance, hgap'⟩
  have hcfg : genuine.cfg = ⟨searchState base c address, outer⟩ := by
    change (searchSystem base c).startCfg search outer = _
    change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
    unfold CounterControlSearchSystem.commandOffset
    rw [show rawCommands.get search = raw by
      exact CounterControlCommandAt.rawCommands_get_rawTag raw hraw]
    rfl
  let replay : ReachedGenuineSearch base c start :=
    ⟨genuine, by simpa [hcfg] using hreach⟩
  exact ⟨replay, rfl, rfl⟩

/-- A later outward validation search paired with an inward guarded search.
The boundary-zero anchor is retained so the remaining outward sweep can be
fed directly to validation reconstruction. -/
structure InwardReplay
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction) : Type where
  zeroTape : FullTM0.Tape (Symbol numTags)
  zero_read : zeroTape.read = boundarySymbol 0
  reaches_outwardStart : FullTM0.Reaches
    (CounterControlNestingBridge.machine base c)
    (foundCfg current.current)
    ⟨searchState base c ⟨growth, source, 4⟩,
      zeroTape.move (orient growth .right)⟩
  replayRaw : RawCommand
  replayRaw_validation : replayRaw ∈
    validationCommands growth source instruction
  replayRaw_mem : replayRaw ∈ rawCommands
  matching_slots : current.selectedRaw.address.slot +
    replayRaw.address.slot = 7
  replay_logicalDirection : replayRaw.logicalSearchDirection = .right
  replay : ReachedGenuineSearch base c (foundCfg current.current)
  replay_search_eq : replay.search =
    CounterControlCommandAt.rawTag replayRaw replayRaw_mem
  replay_outer_eq : replay.outer =
    current.foundTape.move (orient growth .right)
  distance_lt : current.current.distance < replay.distance

private theorem packageReplay
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (currentSlot : Nat) (currentExpected : Fin 5)
    (hcurrentRaw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, currentSlot⟩ currentExpected .left
      (directRef growth source currentSlot) .preserve)
    (zeroTape : FullTM0.Tape (Symbol numTags))
    (hzero : zeroTape.read = boundarySymbol 0)
    (houtwardStart : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 4⟩,
        zeroTape.move (orient growth .right)⟩)
    (replaySlot : Nat) (replayExpected : Fin 5)
    (replaySuccess : ControlRef)
    (hreplayValidation : RawCommand.boundaryNavigation
      ⟨growth, source, replaySlot⟩ replayExpected .right replaySuccess
      .preserve ∈ validationCommands growth source instruction)
    (hslots : currentSlot + replaySlot = 7)
    (hreplayEntry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, replaySlot⟩,
        current.foundTape.move (orient growth .right)⟩) :
    Nonempty (InwardReplay current growth source instruction) := by
  let replayRaw : RawCommand := .boundaryNavigation
    ⟨growth, source, replaySlot⟩ replayExpected .right replaySuccess
      .preserve
  have hreplayRaw : replayRaw ∈ rawCommands :=
    validationCommand_mem growth source instruction hrule
      (by simpa [replayRaw] using hreplayValidation)
  rcases reachedBoundarySearch_of_immortal base c hmortal himmortal
      ⟨growth, source, replaySlot⟩ replayExpected .right replaySuccess
      (by simpa [replayRaw] using hreplayRaw)
      (current.foundTape.move (orient growth .right)) hreplayEntry with
    ⟨replay, hreplaySearch, hreplayOuter⟩
  have hcommand : command base c replay.search =
      CounterControlCommandAt.compileRawCommand base c replayRaw
        hreplayRaw := by
    rw [hreplaySearch]
    rfl
  have hreplayGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary replayExpected).Matches
      (current.foundTape.move (orient growth .right))
      (orient growth .right) replay.distance := by
    have hgap := replay.gap
    rw [hcommand, CounterControlCommandAt.compileRawCommand_spec] at hgap
    simpa [replayRaw, CounterControlCommandAt.compileRawAtTag,
      compileNavigationAction, Command.target, Command.searchDirection,
      hreplayOuter] using hgap
  have hparent := parentGap_of_selectedRaw_boundary current
    ⟨growth, source, currentSlot⟩ currentExpected .left
    (directRef growth source currentSlot) hcurrentRaw
  have hcurrentDirection : current.direction = orient growth .left := by
    have hdirection := current.selectedRaw_direction_eq
    rw [CounterControlCommandAt.compileRawCommand_searchDirection] at hdirection
    rw [hcurrentRaw] at hdirection
    exact hdirection.symm
  have hreplayGap' : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary replayExpected).Matches
      ((current.parentOuter.moveN (orient growth .left)
      (current.current.distance + 1)).move (orient growth .right))
      (orient growth .right) replay.distance := by
    have hfound := current.foundTape_eq_parentMoveN
    rw [hcurrentDirection] at hfound
    rw [hfound] at hreplayGap
    exact hreplayGap
  have hge : current.current.distance + 1 ≤ replay.distance := by
    have := reverseBoundaryGap_distance_ge hparent
      (by simpa only [opposite_orient_left] using hreplayGap')
    exact this
  refine ⟨⟨zeroTape, hzero, houtwardStart, replayRaw,
    by simpa [replayRaw] using hreplayValidation, hreplayRaw, ?_, rfl,
    replay, ?_, hreplayOuter, by omega⟩⟩
  · simpa [hcurrentRaw, replayRaw, RawCommand.address] using hslots
  · simpa [replayRaw] using hreplaySearch

private theorem replay_of_zeroInward
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 3⟩ 0 .left (directRef growth source 3)
        .preserve) :
    Nonempty (InwardReplay current growth source instruction) := by
  have hzero := foundTape_read_of_selectedRaw_boundary current
    ⟨growth, source, 3⟩ 0 .left (directRef growth source 3) hraw
  have hsuccess := current.reaches_selectedRaw_success
  have hsuccess' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (directRef growth source 3), current.foundTape⟩ := by
    simpa [hraw, rawSuccessRef, exactSuccessTape] using hsuccess
  have hcontinuation : RawDirectRule.mk growth
      (directRef growth source 3) (.boundary 0)
      (searchRef growth source 4) .right ∈
        validationRules growth source := by
    simp [validationRules, MarkerValidation.sweep,
      routeContinuationRules, routeContinuationRulesFrom,
      validationSearchBase, validationDirectBase, directRef, searchRef]
  have hreplay := reaches_validationNext_entry base c growth source
    instruction hrule 3 0 .right current.foundTape hzero
    (by simpa using hcontinuation) hsuccess'
  apply packageReplay base c hmortal current growth source instruction hrule
    himmortal 3 0 hraw current.foundTape hzero hreplay
    4 1 (directRef growth source 4)
  · simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
      validationSearchBase, validationDirectBase]
  · omega
  · exact hreplay

private theorem replay_of_oneInward
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 2⟩ 1 .left (directRef growth source 2)
        .preserve) :
    Nonempty (InwardReplay current growth source instruction) := by
  have hone := foundTape_read_of_selectedRaw_boundary current
    ⟨growth, source, 2⟩ 1 .left (directRef growth source 2) hraw
  have hsuccess := current.reaches_selectedRaw_success
  have hsuccess' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (directRef growth source 2), current.foundTape⟩ := by
    simpa [hraw, rawSuccessRef, exactSuccessTape] using hsuccess
  have hentry3 := reaches_validationNext_entry base c growth source
    instruction hrule 2 1 .left current.foundTape hone
    (by
      simp [validationRules, MarkerValidation.sweep,
        routeContinuationRules, routeContinuationRulesFrom,
        validationSearchBase, validationDirectBase, directRef, searchRef])
    hsuccess'
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 3 0 .left .right
      (current.foundTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry3 with ⟨d0, gap0, houtwardStart⟩
  let zeroTape :=
    (current.foundTape.move (orient growth .left)).moveN
      (orient growth .left) d0
  have hzero : zeroTape.read = boundarySymbol 0 := by
    simpa [zeroTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap0.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 4 1 .right .right
      (zeroTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [zeroTape] using houtwardStart) with
    ⟨d1, gap1, hreplay⟩
  have hpair := reverseGap_pair_continue hone gap0
    (by simpa only [zeroTape, opposite_orient_left] using gap1)
  have htape :
      ((zeroTape.move (orient growth .right)).moveN
        (orient growth .right) d1).move (orient growth .right) =
        current.foundTape.move (orient growth .right) := by
    simpa only [zeroTape, opposite_orient_left] using hpair.2
  have hreplay' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 5⟩,
        current.foundTape.move (orient growth .right)⟩ := by
    rw [← htape]
    exact hreplay
  apply packageReplay base c hmortal current growth source instruction hrule
    himmortal 2 1 hraw zeroTape hzero
    (by simpa [zeroTape] using houtwardStart)
    5 2 (directRef growth source 5)
  · simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
      validationSearchBase, validationDirectBase]
  · omega
  · exact hreplay'

private theorem replay_of_twoInward
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 1⟩ 2 .left (directRef growth source 1)
        .preserve) :
    Nonempty (InwardReplay current growth source instruction) := by
  have htwo := foundTape_read_of_selectedRaw_boundary current
    ⟨growth, source, 1⟩ 2 .left (directRef growth source 1) hraw
  have hsuccess := current.reaches_selectedRaw_success
  have hsuccess' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (directRef growth source 1), current.foundTape⟩ := by
    simpa [hraw, rawSuccessRef, exactSuccessTape] using hsuccess
  have hentry2 := reaches_validationNext_entry base c growth source
    instruction hrule 1 2 .left current.foundTape htwo
    (by
      simp [validationRules, MarkerValidation.sweep,
        routeContinuationRules, routeContinuationRulesFrom,
        validationSearchBase, validationDirectBase, directRef, searchRef])
    hsuccess'
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 2 1 .left .left
      (current.foundTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry2 with ⟨d1, gap1, hentry3⟩
  let oneTape :=
    (current.foundTape.move (orient growth .left)).moveN
      (orient growth .left) d1
  have hone : oneTape.read = boundarySymbol 1 := by
    simpa [oneTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap1.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 3 0 .left .right
      (oneTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [oneTape] using hentry3) with
    ⟨d0, gap0, houtwardStart⟩
  let zeroTape :=
    (oneTape.move (orient growth .left)).moveN
      (orient growth .left) d0
  have hzero : zeroTape.read = boundarySymbol 0 := by
    simpa [zeroTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap0.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 4 1 .right .right
      (zeroTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [zeroTape, oneTape] using houtwardStart) with
    ⟨e0, reverse0, hentry5⟩
  have hpair0 := reverseGap_pair_continue hone gap0 (by
      simpa only [zeroTape, opposite_orient_left] using reverse0)
  have htape1 :
      ((zeroTape.move (orient growth .right)).moveN
        (orient growth .right) e0).move (orient growth .right) =
        oneTape.move (orient growth .right) := by
    simpa only [zeroTape, opposite_orient_left] using hpair0.2
  have hentry5' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 5⟩,
        oneTape.move (orient growth .right)⟩ := by
    rw [← htape1]
    exact hentry5
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 5 2 .right .right
      (oneTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry5' with ⟨e1, reverse1, hreplay⟩
  have hpair1 := reverseGap_pair_continue htwo gap1
    (by simpa only [oneTape, opposite_orient_left] using reverse1)
  have htape2 :
      ((oneTape.move (orient growth .right)).moveN
        (orient growth .right) e1).move (orient growth .right) =
        current.foundTape.move (orient growth .right) := by
    simpa only [oneTape, opposite_orient_left] using hpair1.2
  have hreplay' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 6⟩,
        current.foundTape.move (orient growth .right)⟩ := by
    rw [← htape2]
    exact hreplay
  apply packageReplay base c hmortal current growth source instruction hrule
    himmortal 1 2 hraw zeroTape hzero
    (by simpa [zeroTape, oneTape] using houtwardStart)
    6 3 (directRef growth source 6)
  · simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
      validationSearchBase, validationDirectBase]
  · omega
  · exact hreplay'

private theorem replay_of_threeInward
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current))
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 0⟩ 3 .left (directRef growth source 0)
        .preserve) :
    Nonempty (InwardReplay current growth source instruction) := by
  have hthree := foundTape_read_of_selectedRaw_boundary current
    ⟨growth, source, 0⟩ 3 .left (directRef growth source 0) hraw
  have hsuccess := current.reaches_selectedRaw_success
  have hsuccess' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (directRef growth source 0), current.foundTape⟩ := by
    simpa [hraw, rawSuccessRef, exactSuccessTape] using hsuccess
  have hentry1 := reaches_validationNext_entry base c growth source
    instruction hrule 0 3 .left current.foundTape hthree
    (by
      simp [validationRules, MarkerValidation.sweep,
        routeContinuationRules, routeContinuationRulesFrom,
        validationSearchBase, validationDirectBase, directRef, searchRef])
    hsuccess'
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 1 2 .left .left
      (current.foundTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry1 with ⟨d2, gap2, hentry2⟩
  let twoTape :=
    (current.foundTape.move (orient growth .left)).moveN
      (orient growth .left) d2
  have htwo : twoTape.read = boundarySymbol 2 := by
    simpa [twoTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap2.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 2 1 .left .left
      (twoTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [twoTape] using hentry2) with ⟨d1, gap1, hentry3⟩
  let oneTape :=
    (twoTape.move (orient growth .left)).moveN
      (orient growth .left) d1
  have hone : oneTape.read = boundarySymbol 1 := by
    simpa [oneTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap1.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 3 0 .left .right
      (oneTape.move (orient growth .left))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [oneTape, twoTape] using hentry3) with
    ⟨d0, gap0, houtwardStart⟩
  let zeroTape :=
    (oneTape.move (orient growth .left)).moveN
      (orient growth .left) d0
  have hzero : zeroTape.read = boundarySymbol 0 := by
    simpa [zeroTape, FullTM0.Tape.read_moveN, Target.Matches] using
      gap0.marked
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 4 1 .right .right
      (zeroTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      (by simpa [zeroTape, oneTape, twoTape] using houtwardStart) with
    ⟨e0, reverse0, hentry5⟩
  have hpair0 := reverseGap_pair_continue hone gap0 (by
      simpa only [zeroTape, opposite_orient_left] using reverse0)
  have htape1 :
      ((zeroTape.move (orient growth .right)).moveN
        (orient growth .right) e0).move (orient growth .right) =
        oneTape.move (orient growth .right) := by
    simpa only [zeroTape, opposite_orient_left] using hpair0.2
  have hentry5' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 5⟩,
        oneTape.move (orient growth .right)⟩ := by
    rw [← htape1]
    exact hentry5
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 5 2 .right .right
      (oneTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry5' with ⟨e1, reverse1, hentry6⟩
  have hpair1 := reverseGap_pair_continue htwo gap1
    (by simpa only [oneTape, opposite_orient_left] using reverse1)
  have htape2 :
      ((oneTape.move (orient growth .right)).moveN
        (orient growth .right) e1).move (orient growth .right) =
        twoTape.move (orient growth .right) := by
    simpa only [oneTape, opposite_orient_left] using hpair1.2
  have hentry6' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 6⟩,
        twoTape.move (orient growth .right)⟩ := by
    rw [← htape2]
    exact hentry6
  rcases reaches_validationNext_of_immortal base c hmortal growth source
      instruction hrule himmortal 6 3 .right .right
      (twoTape.move (orient growth .right))
      (by
        simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
          validationSearchBase, validationDirectBase])
      (by
        simp [validationRules, MarkerValidation.sweep,
          routeContinuationRules, routeContinuationRulesFrom,
          validationSearchBase, validationDirectBase, directRef, searchRef])
      hentry6' with ⟨e2, reverse2, hreplay⟩
  have hpair2 := reverseGap_pair_continue hthree gap2
    (by simpa only [twoTape, opposite_orient_left] using reverse2)
  have htape3 :
      ((twoTape.move (orient growth .right)).moveN
        (orient growth .right) e2).move (orient growth .right) =
        current.foundTape.move (orient growth .right) := by
    simpa only [twoTape, opposite_orient_left] using hpair2.2
  have hreplay' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨searchState base c ⟨growth, source, 7⟩,
        current.foundTape.move (orient growth .right)⟩ := by
    rw [← htape3]
    exact hreplay
  apply packageReplay base c hmortal current growth source instruction hrule
    himmortal 0 3 hraw zeroTape hzero
    (by simpa [zeroTape, oneTape, twoTape] using houtwardStart)
    7 4 (bodyEntry growth source instruction)
  · simp [validationCommands, MarkerValidation.sweep, routeCommandsAux,
      validationSearchBase, validationDirectBase]
  · omega
  · exact hreplay'

/-- Starting from the exact found state of any guarded inward validation
command, execute the smaller symmetric cycle and stop at the matching
outward generated search.  Its entry lies one cell outward from the original
found boundary, and its genuine gap is strictly longer than the guarded
current gap.

The result also retains reachability to validation slot `4` from the exact
boundary-zero tape.  Thus later code can continue the complete outward sweep
and invoke validation reconstruction without replaying this argument. -/
theorem reaches_matchingReplay_of_inward_validation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (hdirection : current.direction = orient growth .left)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty (InwardReplay current growth source instruction) := by
  rcases selectedRaw_inward_cases current growth source instruction
      hcommand hdirection with hraw | hraw | hraw | hraw
  · exact replay_of_threeInward base c hmortal current growth source
      instruction hrule himmortal hraw
  · exact replay_of_twoInward base c hmortal current growth source
      instruction hrule himmortal hraw
  · exact replay_of_oneInward base c hmortal current growth source
      instruction hrule himmortal hraw
  · exact replay_of_zeroInward base c hmortal current growth source
      instruction hrule himmortal hraw

/-- The inward-validation replay is precisely the strict unguarded-search
branch admitted by the guarded parent dispatcher. -/
theorem foundGuardedEscapeOutcome_of_inward_validation
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GuardedSearch base c)
    (growth : Turing.Dir) (source : Nat)
    (instruction : CounterMachine.Instruction)
    (hrule : (source, instruction) ∈ GlobalSourceProgram.program)
    (hcommand : current.selectedRaw ∈
      validationCommands growth source instruction)
    (hdirection : current.direction = orient growth .left)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)) :
    Nonempty
      (CounterControlGuardedParentContinuation.FoundGuardedEscapeOutcome
        current) := by
  rcases reaches_matchingReplay_of_inward_validation base c hmortal current
      growth source instruction hrule hcommand hdirection himmortal with
    ⟨replay⟩
  exact ⟨CounterControlGuardedParentContinuation.FoundGuardedEscapeOutcome.nextSearch
    replay.replay.toGenuineSearch replay.replay.reaches replay.distance_lt⟩

end

end CounterControlInwardValidationReplay
end Hooper
end Kari
end LeanWang
