/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidation
import LeanWang.Kari.Hooper.CounterControlGenuineDecrementEntry
import LeanWang.Kari.Hooper.CounterControlGuardedCleanupProgress
import LeanWang.Kari.Hooper.CounterControlGuardedShiftEmbedding
import LeanWang.Kari.Hooper.CounterControlValidationRoundtrip

/-!
# Outward arbitrary validation callers

The outward half of an arbitrary validation call has not yet seen boundary
`0`, so it cannot reconstruct the current instruction body as a complete
core.  This file continues such calls through the instruction and compares
their retained blank gap with the complete core reconstructed by the next
validation round.

The first specialization is the final outward command followed by a clock
increment.  It is the smallest nontrivial case: validation ends exactly on
boundary `4`, and the instruction begins with a distance-zero shift of that
boundary.  The destination may still be occupied, so success and collision
are treated separately.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutward

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge CounterControlSearchSystem
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlGenuineValidation
open CounterControlResumedShiftCoordinates
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The singleton shift which implements a clock increment. -/
def clockIncrementRaw (growth : Turing.Dir) (source : Nat) : RawCommand :=
  .markerShift ⟨growth, source, bodySearchBase⟩ 4 .left .right
    (directRef growth source bodyDirectBase) (some .left)
    (some (directRef growth source testDirectSlot))

theorem clockIncrementRaw_mem_increment
    (growth : Turing.Dir) (source : Nat) :
    clockIncrementRaw growth source ∈
      incrementShiftCommands growth source .clock := by
  simp [clockIncrementRaw, incrementShiftCommands,
    incrementShiftCommandsAux, MarkerShift.incrementOrder]

theorem clockIncrementRaw_mem
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program) :
    clockIncrementRaw growth source ∈ rawCommands := by
  apply CounterControlInstructionSemantics.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, incrementCommands,
    clockIncrementRaw_mem_increment growth source]

theorem clockIncrementRaw_target
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : clockIncrementRaw growth source ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (clockIncrementRaw growth source) hraw).target = Target.boundary 4 := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [clockIncrementRaw, CounterControlCommandAt.compileRawAtTag,
    Command.target]

theorem clockIncrementRaw_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat)
    (hraw : clockIncrementRaw growth source ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (clockIncrementRaw growth source) hraw).searchDirection =
        orient growth .left := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [clockIncrementRaw, CounterControlCommandAt.compileRawAtTag,
    Command.searchDirection]

/-- The last outward validation caller advertises its boundary-`4` gap in
the physical outward direction. -/
theorem outwardFour_gap
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

/-- Exact physical direction of the last outward validation search. -/
theorem outwardFour_direction
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

/-- The exact found tape of the last outward validation caller is centered
on boundary `4`. -/
theorem outwardFour_foundTape_read
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

/-- The boundary-`4` tape delivered by the last outward validation command
is an immediate genuine entry to the singleton clock shift. -/
def immediateClockShift
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    GenuineSearch base c :=
  let hmem := clockIncrementRaw_mem growth source next hrule
  CounterControlGenuineDecrementEntry.immediateSearch base c
    (clockIncrementRaw growth source) hmem current.foundTape (by
      rw [clockIncrementRaw_target]
      simpa [Target.Matches] using hread)

@[simp] theorem immediateClockShift_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateClockShift base c current growth source next hrule hread).cfg =
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape⟩ := by
  simp [immediateClockShift,
    CounterControlGenuineDecrementEntry.immediateSearch_cfg,
    clockIncrementRaw, RawCommand.address]

@[simp] theorem immediateClockShift_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateClockShift base c current growth source next hrule hread).selectedRaw =
      clockIncrementRaw growth source := by
  simp [immediateClockShift,
    CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw]

@[simp] theorem immediateClockShift_foundTape
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateClockShift base c current growth source next hrule
        hread).foundTape = current.foundTape := by
  simp [immediateClockShift,
    CounterControlGenuineDecrementEntry.immediateSearch,
    GenuineSearch.foundTape]

/-! ## Tape geometry of one outward shift -/

/-- Move a boundary one cell in `direction`, and center the result on the
new boundary.  The implementation is expressed through the common exact
shift-step tape so it can be used directly at instruction endpoints. -/
def outwardShiftedTape
    (direction : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat) (expected : Fin 5) :
    FullTM0.Tape (Symbol numTags) :=
  (shiftStepTape (NestingMachine.opposite direction)
      (outer.moveN direction distance) 0 expected).move direction

/-- The same shifted tape, recentered at the origin of the old gap. -/
def outwardShiftedOuter
    (direction : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat) (expected : Fin 5) :
    FullTM0.Tape (Symbol numTags) :=
  (outwardShiftedTape direction outer distance expected).moveN
    (NestingMachine.opposite direction) (distance + 1)

/-- Recentring the shifted tape back at the old origin and then traversing
the enlarged gap returns to the exact shifted endpoint. -/
theorem outwardShiftedOuter_found
    (direction : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat) (expected : Fin 5) :
    (outwardShiftedOuter direction outer distance expected).moveN
        direction (distance + 1) =
      outwardShiftedTape direction outer distance expected := by
  have hcancel := CanonicalInitializerProgram.moveN_opposite
    (outwardShiftedTape direction outer distance expected)
    (NestingMachine.opposite direction) (distance + 1)
  cases direction <;>
    simpa [outwardShiftedOuter, NestingMachine.opposite] using hcancel

/-- Moving the marked end of a genuine blank gap one cell outward produces
a genuine blank gap one cell longer when viewed from the old origin. -/
theorem outwardShiftedOuter_gap
    (direction : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat) (expected : Fin 5)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches outer direction distance) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches
      (outwardShiftedOuter direction outer distance expected)
      direction (distance + 1) := by
  constructor
  · intro i hi
    by_cases heq : i = distance
    · subst i
      cases direction <;>
        simp [outwardShiftedOuter, outwardShiftedTape, shiftStepTape,
          NestingMachine.opposite,
          FullTM0.Tape.move, FullTM0.Tape.moveN, FullTM0.Tape.offset,
          FullTM0.Tape.write]
    · have hlt : i < distance := by omega
      have hblank := hgap.blank hlt
      cases direction <;>
        simp [outwardShiftedOuter, outwardShiftedTape, shiftStepTape,
          NestingMachine.opposite,
          FullTM0.Tape.move, FullTM0.Tape.moveN, FullTM0.Tape.offset,
          FullTM0.Tape.write] <;>
        split_ifs <;> try omega
      all_goals
        convert hblank using 1
        all_goals simp [FullTM0.Tape.offset]
        all_goals ring_nf
  · cases direction <;>
      simp [outwardShiftedOuter, outwardShiftedTape, shiftStepTape,
        NestingMachine.opposite, Target.Matches,
        FullTM0.Tape.move, FullTM0.Tape.moveN, FullTM0.Tape.offset,
        FullTM0.Tape.write]

/-- Once the shifted boundary is identified with canonical boundary `4`,
the whole old gap lies strictly inside the reconstructed core. -/
theorem outwardShifted_distance_lt_layoutEnd
    (growth : Turing.Dir) (outer : FullTM0.Tape (Symbol numTags))
    (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches outer
      (orient growth .right) distance)
    (registers : Registers) (coreTape : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : outwardShiftedTape (orient growth .right) outer distance 4 =
      atLogical growth coreTape (layoutEnd registers)) :
    distance < layoutEnd registers := by
  have hshiftedGap := outwardShiftedOuter_gap
    (orient growth .right) outer distance (4 : Fin 5) hgap
  have hfound :
      (outwardShiftedOuter (orient growth .right) outer distance 4).moveN
          (orient growth .right) (distance + 1) =
        atLogical growth coreTape (boundaryOffset registers 4) := by
    rw [outwardShiftedOuter_found, hcenter, boundaryOffset_four]
  have hlong : distance + 1 < layoutEnd registers :=
    rightGap_distance_lt_layoutEnd hcore (3 : Fin 4) (distance + 1)
      hshiftedGap hfound
  omega

/-- The exact success tape of the singleton clock shift, after its following
logical direct move, is the outward-shifted tape above. -/
theorem clockIncrementSuccessTape_eq_outwardShiftedTape
    (growth : Turing.Dir) (source : Nat)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat) :
    (exactSuccessTape (clockIncrementRaw growth source)
        (outer.moveN (orient growth .right) distance)).move
        (orient growth .right) =
      outwardShiftedTape (orient growth .right) outer distance 4 := by
  cases growth <;>
    simp [exactSuccessTape, clockIncrementRaw, outwardShiftedTape,
      shiftStepTape, orient, NestingMachine.opposite]

/-- The blank continuation after a successful singleton clock shift enters
the target logical counter state on the shifted boundary-`4` tape. -/
theorem reaches_logical_of_clockIncrementSuccess
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags)) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source bodyDirectBase),
        exactSuccessTape (clockIncrementRaw growth source) T⟩
      ⟨logicalState base c growth next,
        (exactSuccessTape (clockIncrementRaw growth source) T).move
          (orient growth .right)⟩ := by
  let rule : RawDirectRule :=
    ⟨growth, directRef growth source bodyDirectBase, .blank,
      .logical growth next, .right⟩
  have hmem : rule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change rule ∈ validationRules growth source ++
      incrementRules growth source next .clock
    apply List.mem_append_right
    simp only [incrementRules, List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    simp [rule, AnchoredCounterGeometry.routeFromIncrement]
  have hmatch : rule.read.Matches
      (exactSuccessTape (clockIncrementRaw growth source) T).read := by
    cases growth <;>
      simp [rule, RawRead.Matches, exactSuccessTape,
        clockIncrementRaw, orient, FullTM0.Tape.read,
        FullTM0.Tape.move, FullTM0.Tape.write]
  have hrun := CounterControlDirectSemantics.reaches_directRule
    base c rule hmem
      (exactSuccessTape (clockIncrementRaw growth source) T) hmatch
  simpa [CounterControlNestingBridge.machine,
    BoundedMarkerProgram.machine, CounterControlPlan.table, rule,
    CounterControlPlan.resolve] using hrun

/-- The nonblank collision continuation returns from the occupied
destination to the cleared old boundary and enters cleanup stage `3`. -/
theorem reaches_cleanup_of_clockIncrementCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hoccupied : ShiftDestinationOccupied
      (clockIncrementRaw growth source) T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape (clockIncrementRaw growth source) T⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        T.write blankSymbol⟩ := by
  let rule : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot, .nonblank,
      searchRef growth source cleanupSearchBase, .left⟩
  have hmem : rule ∈ rawDirectRules := by
    apply CounterControlInstructionSemantics.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change rule ∈ validationRules growth source ++
      incrementRules growth source next .clock
    apply List.mem_append_right
    simp [rule, incrementRules]
  have hmatch : rule.read.Matches
      (exactCollisionTape (clockIncrementRaw growth source) T).read := by
    simpa [rule, RawRead.Matches, ShiftDestinationOccupied,
      clockIncrementRaw, exactCollisionTape] using hoccupied
  have hrun := CounterControlDirectSemantics.reaches_directRule
    base c rule hmem
      (exactCollisionTape (clockIncrementRaw growth source) T) hmatch
  have hrun' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape (clockIncrementRaw growth source) T⟩
      ⟨resolve base c (searchRef growth source cleanupSearchBase),
        (exactCollisionTape (clockIncrementRaw growth source) T).move
          (orient growth .left)⟩ := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table, rule,
      CounterControlPlan.resolve] using hrun
  have htape :
      (exactCollisionTape (clockIncrementRaw growth source) T).move
          (orient growth .left) = T.write blankSymbol := by
    cases growth <;>
      funext position <;>
      simp [exactCollisionTape, clockIncrementRaw, orient,
        FullTM0.Tape.move, FullTM0.Tape.write]
  rw [htape] at hrun'
  simpa [searchRef, CounterControlPlan.resolve] using hrun'

/-- Package a genuine cleanup-stage-`3` gap under the exact generated raw
command used by collision recovery. -/
def cleanupThreeSearch
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (3 : Fin 5)).Matches outer
      (orient growth .left) distance) : GenuineSearch base c := by
  let raw := CounterControlCleanupRoute.command growth source
    CounterControlCleanupRoute.Stage.three
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source .clock next hrule CounterControlCleanupRoute.Stage.three
  let search : Search := CounterControlCommandAt.rawTag raw hmem
  exact {
    search := search
    outer := outer
    distance := distance
    gap := by
      have hcommand : CounterControlSearchSystem.command base c search =
          CounterControlCommandAt.compileRawCommand base c raw hmem := rfl
      rw [hcommand, CounterControlCleanupRoute.compile_command]
      simpa [raw, CounterControlCleanupRoute.Stage.expected,
        Command.target, Command.searchDirection] using hgap }

@[simp] theorem cleanupThreeSearch_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (3 : Fin 5)).Matches outer
      (orient growth .left) distance) :
    (cleanupThreeSearch base c growth source next hrule outer distance
        hgap).cfg =
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩, outer⟩ := by
  let raw := CounterControlCleanupRoute.command growth source
    CounterControlCleanupRoute.Stage.three
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source .clock next hrule CounterControlCleanupRoute.Stage.three
  let search : Search := CounterControlCommandAt.rawTag raw hmem
  have hget : rawCommands.get search = raw :=
    CounterControlCommandAt.rawCommands_get_rawTag raw hmem
  change (searchSystem base c).startCfg search outer = _
  change (⟨CounterControlSearchSystem.commandOffset base c search, outer⟩ :
    FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
  unfold CounterControlSearchSystem.commandOffset
  rw [hget]
  rfl

@[simp] theorem cleanupThreeSearch_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat)
    (hrule : (source, .increment .clock next) ∈
      GlobalSourceProgram.program)
    (outer : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (3 : Fin 5)).Matches outer
      (orient growth .left) distance) :
    (cleanupThreeSearch base c growth source next hrule outer distance
        hgap).selectedRaw =
      CounterControlCleanupRoute.command growth source
        CounterControlCleanupRoute.Stage.three := by
  let raw := CounterControlCleanupRoute.command growth source
    CounterControlCleanupRoute.Stage.three
  let hmem := CounterControlCleanupRoute.command_mem_rawCommands_of_increment
    growth source .clock next hrule CounterControlCleanupRoute.Stage.three
  change rawCommands.get (CounterControlCommandAt.rawTag raw hmem) = raw
  exact CounterControlCommandAt.rawCommands_get_rawTag raw hmem

/-! ## Tape geometry of collision cleanup -/

/-- If the marked end of a blank gap is cleared, any boundary found by
searching backward from that cell must lie strictly beyond the old origin.
The cleared endpoint supplies the strict extra cell. -/
theorem clearedReverseGap_distance_gt
    {outer : FullTM0.Tape (Symbol numTags)} {direction : Turing.Dir}
    {distance reverseDistance : Nat} {target replayTarget : Fin 5}
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches outer direction distance)
    (hreverse : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary replayTarget).Matches
      ((outer.moveN direction distance).write blankSymbol)
      (NestingMachine.opposite direction) reverseDistance) :
    distance < reverseDistance := by
  by_contra hnot
  have hle : reverseDistance ≤ distance := Nat.le_of_not_gt hnot
  cases reverseDistance with
  | zero =>
      have hmarked := hreverse.marked
      have hboundary :
          ((outer.moveN direction distance).write blankSymbol).read =
            boundarySymbol replayTarget := by
        simpa [FullTM0.Tape.read_moveN, Target.Matches] using hmarked
      have hblank :
          ((outer.moveN direction distance).write blankSymbol).read =
            blankSymbol := by simp
      rw [hblank] at hboundary
      exact blankSymbol_ne_boundarySymbol replayTarget hboundary
  | succ reverseDistance =>
      let index := distance - (reverseDistance + 1)
      have hindex : index < distance := by
        dsimp [index]
        omega
      have hblank := hgap.blank hindex
      have hmarked := hreverse.marked
      have hboundary :
          (((outer.moveN direction distance).write blankSymbol).moveN
              (NestingMachine.opposite direction)
              (reverseDistance + 1)).read =
            boundarySymbol replayTarget := by
        simpa [FullTM0.Tape.read_moveN, Target.Matches] using hmarked
      have hread :
          (((outer.moveN direction distance).write blankSymbol).moveN
              (NestingMachine.opposite direction)
              (reverseDistance + 1)).read =
            outer (FullTM0.Tape.offset direction index) := by
        cases direction <;>
          simp [FullTM0.Tape.read, FullTM0.Tape.moveN,
            FullTM0.Tape.offset, FullTM0.Tape.write,
            NestingMachine.opposite, index] <;>
          split_ifs <;> try omega
        all_goals
          apply congrArg outer
          omega
      rw [hread] at hboundary
      rw [hboundary] at hblank
      exact blankSymbol_ne_boundarySymbol replayTarget hblank.symm

private theorem reaches_trans
    (base : Nat) (c : Nat.Partrec.Code)
    {first second third : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}
    (hfirst : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first second)
    (hsecond : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) second third) :
    FullTM0.Reaches
      (CounterControlNestingBridge.machine base c) first third := by
  unfold FullTM0.Reaches at hfirst hsecond ⊢
  exact hfirst.trans hsecond

end

end CounterControlGenuineValidationOutward
end Hooper
end Kari
end LeanWang
