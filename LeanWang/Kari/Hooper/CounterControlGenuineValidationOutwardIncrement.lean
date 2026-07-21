/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutward
import LeanWang.Kari.Hooper.CounterControlGenuineValidationOutwardSuffix
import LeanWang.Kari.Hooper.CounterControlGuardedIncrementEmbedding
import LeanWang.Kari.Hooper.CounterControlGuardedDecrementPositiveEmbedding
import LeanWang.Kari.Hooper.CounterControlOutwardGapTransport
import LeanWang.Kari.Hooper.CounterControlOutwardRoute

/-!
# Final outward validation followed by an arbitrary increment

The first command of every increment schedule moves boundary `4` one cell
outward.  If that destination is occupied, all registers use the same cleanup
exit.  Otherwise the remaining shifts run inward.  Their first search is for
boundary `3`; the old final-validation gap is still blank on that whole ray,
so its distance is strictly smaller than the first remaining shift distance.
The canonical backward geometry of the completed schedule places that
distance inside the reconstructed incremented core.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGenuineValidationOutwardIncrement

open Turing CounterMachine
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlBridge CounterControlSearchSystem
open CounterControlCoreFrame CounterControlPrefixInstructionResolution
open CounterControlGlobalUnnesting CounterControlParentContinuation
open CounterControlGuardedParentContinuation
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlGenuineValidation
open CounterControlGenuineValidationOutward
open CounterControlGenuineValidationOutwardSuffix
open CounterControlRouteSuffixMortality
open CounterControlGuardedSearch
open CounterControlGuardedSearch.GuardedSearch
open CounterControlGuardedShiftCompletion
open CounterControlGuardedShiftEmbedding
open CounterControlGuardedIncrementEmbedding
open CounterControlGuardedDecrementPositiveEmbedding
open CounterControlOutwardGapTransport
open CounterControlOutwardRoute
open CounterControlResumedShiftCoordinates
open CounterControlResumedRouteEmbedding

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

/-- The first boundary-`4` shift of every increment schedule. -/
def firstIncrementRaw (growth : Turing.Dir) (source : Nat)
    (register : Register) : RawCommand :=
  .markerShift ⟨growth, source, bodySearchBase⟩ 4 .left .right
    (match register with
      | .clock => directRef growth source bodyDirectBase
      | _ => searchRef growth source (bodySearchBase + 1))
    (some .left) (some (directRef growth source testDirectSlot))

def incrementRemaining : Register → List (Fin 5)
  | .left => [3, 2, 1]
  | .right => [3, 2]
  | .temp => [3]
  | .clock => []

theorem firstIncrementRaw_mem_increment
    (growth : Turing.Dir) (source : Nat) (register : Register) :
    firstIncrementRaw growth source register ∈
      incrementShiftCommands growth source register := by
  cases register <;>
    simp [firstIncrementRaw, incrementShiftCommands,
      incrementShiftCommandsAux, MarkerShift.incrementOrder]

theorem firstIncrementRaw_mem
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program) :
    firstIncrementRaw growth source register ∈ rawCommands := by
  apply CounterControlPlan.command_mem_rawCommands_of_rule
    growth hrule
  simp [commandsForRule, incrementCommands,
    firstIncrementRaw_mem_increment growth source register]

theorem firstIncrementRaw_target
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hraw : firstIncrementRaw growth source register ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstIncrementRaw growth source register) hraw).target =
        Target.boundary 4 := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstIncrementRaw, CounterControlCommandAt.compileRawAtTag,
    Command.target]

theorem firstIncrementRaw_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source : Nat) (register : Register)
    (hraw : firstIncrementRaw growth source register ∈ rawCommands) :
    (CounterControlCommandAt.compileRawCommand base c
      (firstIncrementRaw growth source register) hraw).searchDirection =
        orient growth .left := by
  rw [CounterControlCommandAt.compileRawCommand_spec]
  simp [firstIncrementRaw, CounterControlCommandAt.compileRawAtTag,
    Command.searchDirection]

/-- Every increment register uses the same collision exit from its first
boundary-`4` shift.  The exit returns to the cleared old boundary and enters
cleanup stage `3`. -/
theorem reaches_cleanup_of_firstIncrementCollision
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hoccupied : ShiftDestinationOccupied
      (firstIncrementRaw growth source register) T) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape (firstIncrementRaw growth source register) T⟩
      ⟨searchState base c ⟨growth, source, cleanupSearchBase⟩,
        T.write blankSymbol⟩ := by
  let rule : RawDirectRule :=
    ⟨growth, directRef growth source testDirectSlot, .nonblank,
      searchRef growth source cleanupSearchBase, .left⟩
  have hmem : rule ∈ rawDirectRules := by
    apply CounterControlPlan.directRule_mem_rawDirectRules_of_rule
      growth hrule
    change rule ∈ validationRules growth source ++
      incrementRules growth source next register
    apply List.mem_append_right
    simp [rule, incrementRules]
  have hmatch : rule.read.Matches
      (exactCollisionTape
        (firstIncrementRaw growth source register) T).read := by
    simpa [rule, RawRead.Matches, ShiftDestinationOccupied,
      firstIncrementRaw, exactCollisionTape] using hoccupied
  have hrun := CounterControlDirectSemantics.reaches_directRule
    base c rule hmem
      (exactCollisionTape (firstIncrementRaw growth source register) T)
      hmatch
  have hrun' : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      ⟨resolve base c (directRef growth source testDirectSlot),
        exactCollisionTape (firstIncrementRaw growth source register) T⟩
      ⟨resolve base c (searchRef growth source cleanupSearchBase),
        (exactCollisionTape
          (firstIncrementRaw growth source register) T).move
            (orient growth .left)⟩ := by
    simpa [CounterControlNestingBridge.machine,
      BoundedMarkerProgram.machine, CounterControlPlan.table, rule,
      CounterControlPlan.resolve] using hrun
  have htape :
      (exactCollisionTape
        (firstIncrementRaw growth source register) T).move
          (orient growth .left) = T.write blankSymbol := by
    cases growth <;>
      funext position <;>
      simp [exactCollisionTape, firstIncrementRaw, orient,
        FullTM0.Tape.move, FullTM0.Tape.write]
  rw [htape] at hrun'
  simpa [searchRef, CounterControlPlan.resolve] using hrun'

/-- The retained gap of a final outward validation command, for any
incremented register. -/
theorem outwardFour_increment_gap
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source (.increment register next)) .preserve) :
    SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches current.outer
      (orient growth .right) current.distance := by
  have hgap := current.gap
  rw [← current.compileRawCommand_selectedRaw,
    CounterControlCommandAt.compileRawCommand_spec] at hgap
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target,
    Command.searchDirection] using hgap

theorem outwardFour_increment_direction
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source (.increment register next)) .preserve) :
    current.direction = orient growth .right := by
  have hdirection := current.selectedRaw_direction_eq
  rw [CounterControlCommandAt.compileRawCommand_searchDirection]
    at hdirection
  rw [hraw] at hdirection
  exact hdirection.symm

theorem outwardFour_increment_foundTape_read
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source (.increment register next)) .preserve) :
    current.foundTape.read = boundarySymbol 4 := by
  have hmatch := current.selectedRaw_target_matches_foundTape
  rw [CounterControlCommandAt.compileRawCommand_spec] at hmatch
  simpa [hraw, CounterControlCommandAt.compileRawAtTag,
    compileNavigationAction, Command.target, Target.Matches] using hmatch

/-- The boundary-`4` endpoint is an immediate genuine entry to the first
increment shift. -/
def immediateIncrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    GenuineSearch base c :=
  let hmem := firstIncrementRaw_mem growth source next register hrule
  CounterControlGenuineDecrementEntry.immediateSearch base c
    (firstIncrementRaw growth source register) hmem current.foundTape (by
      rw [firstIncrementRaw_target]
      simpa [Target.Matches] using hread)

@[simp] theorem immediateIncrementShift_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).cfg =
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩,
        current.foundTape⟩ := by
  simp [immediateIncrementShift,
    CounterControlGenuineDecrementEntry.immediateSearch_cfg,
    firstIncrementRaw, RawCommand.address]

@[simp] theorem immediateIncrementShift_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).selectedRaw = firstIncrementRaw growth source register := by
  simp [immediateIncrementShift,
    CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw]

@[simp] theorem immediateIncrementShift_distance
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).distance = 0 := by
  simp [immediateIncrementShift]

@[simp] theorem immediateIncrementShift_foundTape
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).foundTape = current.foundTape := by
  simp [immediateIncrementShift,
    CounterControlGenuineDecrementEntry.immediateSearch,
    GenuineSearch.foundTape]

@[simp] theorem immediateIncrementShift_outer
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).outer = current.foundTape := by
  rfl

theorem immediateIncrementShift_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4) :
    (immediateIncrementShift base c current growth source next register
      hrule hread).direction = orient growth .left := by
  unfold immediateIncrementShift
  rw [CounterControlGenuineDecrementEntry.immediateSearch_direction]
  exact firstIncrementRaw_direction base c growth source register _

/-! ## Immediate entry from a completed outward suffix -/

def bodyIncrementShift
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) : GenuineSearch base c :=
  let hmem := firstIncrementRaw_mem growth source next register hrule
  CounterControlGenuineDecrementEntry.immediateSearch base c
    (firstIncrementRaw growth source register) hmem T (by
      rw [firstIncrementRaw_target]
      simpa [Target.Matches] using hread)

@[simp] theorem bodyIncrementShift_cfg
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) :
    (bodyIncrementShift base c growth source next register hrule T hread).cfg =
      ⟨searchState base c ⟨growth, source, bodySearchBase⟩, T⟩ := by
  simp [bodyIncrementShift,
    CounterControlGenuineDecrementEntry.immediateSearch_cfg,
    firstIncrementRaw, RawCommand.address]

@[simp] theorem bodyIncrementShift_selectedRaw
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) :
    (bodyIncrementShift base c growth source next register hrule T
      hread).selectedRaw = firstIncrementRaw growth source register := by
  simp [bodyIncrementShift,
    CounterControlGenuineDecrementEntry.immediateSearch_selectedRaw]

@[simp] theorem bodyIncrementShift_outer
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) :
    (bodyIncrementShift base c growth source next register hrule T
      hread).outer = T := rfl

@[simp] theorem bodyIncrementShift_distance
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) :
    (bodyIncrementShift base c growth source next register hrule T
      hread).distance = 0 := rfl

theorem bodyIncrementShift_direction
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4) :
    (bodyIncrementShift base c growth source next register hrule T
      hread).direction = orient growth .left := by
  unfold bodyIncrementShift
  rw [CounterControlGenuineDecrementEntry.immediateSearch_direction]
  exact firstIncrementRaw_direction base c growth source register _

def guardedBodyIncrement
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4)
    (hblank : (T.move (orient growth .right)).read = blankSymbol) :
    GuardedSearch base c := by
  let shift := bodyIncrementShift base c growth source next register hrule T
    hread
  refine ⟨shift, ?_⟩
  change (shift.outer.move
    (NestingMachine.opposite shift.direction)).read = blankSymbol
  rw [bodyIncrementShift_direction, bodyIncrementShift_outer]
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by cases growth <;> rfl
  rw [hopposite]
  exact hblank

@[simp] theorem guardedBodyIncrement_current
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4)
    (hblank : (T.move (orient growth .right)).read = blankSymbol) :
    (guardedBodyIncrement base c growth source next register hrule T hread
      hblank).current =
      bodyIncrementShift base c growth source next register hrule T hread :=
  rfl

/-- A position witness for the selected shift entered from a completed
validation suffix is the head of the increment schedule. -/
theorem bodyIncrementShift_position
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4)
    (position : IncrementShiftPosition growth source bodySearchBase true
      (MarkerShift.incrementOrder register)
      (bodyIncrementShift base c growth source next register hrule T
        hread).selectedRaw) :
    position.before = [] ∧ position.current = 4 ∧
      position.remaining = incrementRemaining register := by
  have haddress := congrArg RawCommand.address position.raw_eq
  simp only [bodyIncrementShift_selectedRaw] at haddress
  simp [firstIncrementRaw, RawCommand.address] at haddress
  have hbefore : position.before = [] := haddress
  have hlabels := position.labels_eq
  rw [hbefore] at hlabels
  cases register <;>
    simp [MarkerShift.incrementOrder, incrementRemaining] at hlabels ⊢ <;>
    aesop

/-- The first successful shift entered from a completed validation suffix
is the pure one-cell outward move used by `firstIncrementAgreement`. -/
theorem guardedBodyIncrement_shiftedParentBacking
    (base : Nat) (c : Nat.Partrec.Code)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (T : FullTM0.Tape (Symbol numTags))
    (hread : T.read = boundarySymbol 4)
    (hblank : (T.move (orient growth .right)).read = blankSymbol)
    (expected : Fin 5) :
    (guardedBodyIncrement base c growth source next register hrule T hread
      hblank).shiftedParentBacking expected =
      shiftStepTape (orient growth .left)
        (T.move (orient growth .right)) 1 expected := by
  let shift := bodyIncrementShift base c growth source next register hrule T
    hread
  let guarded := guardedBodyIncrement base c growth source next register
    hrule T hread hblank
  have hshiftDirection : shift.direction = orient growth .left :=
    bodyIncrementShift_direction base c growth source next register hrule T
      hread
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  unfold GuardedSearch.shiftedParentBacking GuardedSearch.parentOuter
  change shiftStepTape guarded.direction
      (guarded.current.outer.move
        (NestingMachine.opposite guarded.direction))
      (guarded.current.distance + 1) expected = _
  rw [show guarded.direction = shift.direction by rfl]
  rw [show guarded.current = shift by rfl]
  rw [hshiftDirection, hopposite]
  dsimp [shift]

private theorem outwardFound_moveN_left
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (distance : Nat) :
    (((T.move (orient growth .right)).moveN
      (orient growth .right) distance).moveN
        (orient growth .left) (distance + 1)) = T := by
  funext position
  cases growth <;>
    simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
      FullTM0.Tape.offset] <;>
    congr 1 <;> omega

/-- Mirrored counterpart of decrement's `ShiftedAgainst.advance`: pair one
rightward validation leg with the following leftward increment shift. -/
theorem shiftedAgainst_retreat
    {growth : Turing.Dir} {lower : Fin 4}
    {shiftedUpper lowerOriginal : FullTM0.Tape (Symbol numTags)}
    {routeDistance shiftDistance : Nat}
    (agreement : ShiftedAgainst (orient growth .left) lower.succ
      shiftedUpper
      ((lowerOriginal.move (orient growth .right)).moveN
        (orient growth .right) routeDistance))
    (lowerRead : lowerOriginal.read = boundarySymbol lower.castSucc)
    (routeGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary lower.succ).Matches
      (lowerOriginal.move (orient growth .right))
      (orient growth .right) routeDistance)
    (shiftGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary lower.castSucc).Matches shiftedUpper
      (orient growth .left) shiftDistance)
    (shiftPositive : 0 < shiftDistance) :
    ShiftedAgainst (orient growth .left) lower.castSucc
      (shiftStepTape (orient growth .left) shiftedUpper shiftDistance
        lower.castSucc) lowerOriginal := by
  have hdistance : shiftDistance = routeDistance + 1 := by
    apply BoundedMarkerProgram.boundaryGap_distance_unique shiftGap
    constructor
    · intro k hk
      by_cases hkzero : k = 0
      · subst k
        simpa [FullTM0.Tape.read_moveN] using agreement.blank
      · have hpositive : 0 < k := by omega
        have hahead := agreement.ahead k hpositive
        have hroute :
            ((((lowerOriginal.move (orient growth .right)).moveN
              (orient growth .right) routeDistance).moveN
                (orient growth .left) k).read) = blankSymbol := by
          have hkle : k ≤ routeDistance := by omega
          have hindex : routeDistance - k < routeDistance := by omega
          have hblank := routeGap.blank hindex
          have hcast : ((routeDistance - k : Nat) : Int) =
              (routeDistance : Int) - (k : Int) := by omega
          cases growth <;>
            simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
              FullTM0.Tape.offset, hcast] at hblank ⊢ <;>
            convert hblank using 1 <;> ring_nf
        simpa [FullTM0.Tape.read_moveN] using hahead.trans hroute
    · have hread : (shiftedUpper.moveN (orient growth .left)
          (routeDistance + 1)).read = boundarySymbol lower.castSucc := by
        rw [agreement.ahead (routeDistance + 1) (by omega),
          outwardFound_moveN_left, lowerRead]
      simpa [Target.Matches, FullTM0.Tape.read_moveN] using hread
  subst shiftDistance
  refine ⟨CounterControlGuardedDecrementPositiveEmbedding.shiftStepTape_read_blank
    _ _ _ _, ?_, ?_⟩
  · exact CounterControlGuardedShiftEmbedding.shiftStepTape_destination
      _ _ _ _
  · intro k hk
    rw [CounterControlGuardedDecrementPositiveEmbedding.shiftStepTape_ahead
      _ _ _ _ k hk]
    calc
      ((shiftedUpper.moveN (orient growth .left)
          (routeDistance + 1)).moveN
            (orient growth .left) k).read =
          (shiftedUpper.moveN (orient growth .left)
            (routeDistance + 1 + k)).read := by
              rw [FullTM0.Tape.moveN_add]
      _ = ((((lowerOriginal.move (orient growth .right)).moveN
            (orient growth .right) routeDistance).moveN
              (orient growth .left) (routeDistance + 1 + k)).read) :=
        agreement.ahead _ (by omega)
      _ = (lowerOriginal.moveN (orient growth .left) k).read := by
        rw [show routeDistance + 1 + k = (routeDistance + 1) + k by omega,
          ← FullTM0.Tape.moveN_add, outwardFound_moveN_left]

/-! ## Splitting a consecutive outward route -/

/-- Reverse the part of an outward validation route lying strictly below
the increment's terminal shifted boundary.  The first leg consumes the
newly cleared old boundary; every later leg is an ordinary canonical
inward-ray transport. -/
theorem inwardAgreement_of_terminalIncrement
    {growth : Turing.Dir} {source target : Fin 5}
    {route : List MarkerValidation.Leg}
    (hroute : ToUpper source target route)
    (hstrict : (source : Nat) < (target : Nat))
    {start finish shifted coreTape : FullTM0.Tape (Symbol numTags)}
    (hread : start.read = boundarySymbol source)
    (htrace : CounterControlRouteSuffixMortality.RouteTailGaps growth route
      start finish)
    (terminal : ShiftedAgainst (orient growth .left) target shifted finish)
    {registers : Registers}
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : shifted.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers target)) :
    ∀ back,
      ((atLogical growth coreTape (boundaryOffset registers source)).moveN
        (orient growth .left) back).read =
      (start.moveN (orient growth .left) back).read := by
  induction hroute generalizing start finish shifted with
  | here => simp at hstrict
  | @step i endpoint rest tail ih =>
      cases htrace with
      | cons _ _ start finish trace =>
          rcases routeGaps_uncons growth ⟨i.succ, .right⟩ _ _ _ trace with
            ⟨distance, gap, restTrace⟩
          let oldUpper :=
            ((start.move (orient growth .right)).moveN
              (orient growth .right) distance)
          have holdUpper :
              (start.move (orient growth .right)).moveN
                (orient growth .right) distance = oldUpper := rfl
          have hupperRead : oldUpper.read = boundarySymbol i.succ := by
            change (Target.boundary i.succ).Matches oldUpper.read
            simpa [oldUpper, FullTM0.Tape.read_moveN] using gap.marked
          by_cases hterminal : endpoint = i.succ
          · cases hterminal
            have hrest : rest = ([] : List MarkerValidation.Leg) :=
              ToUpper.eq_nil_of_same tail
            rw [hrest] at restTrace
            cases restTrace
            have hclearedCanonical : shifted =
                atLogical growth coreTape (lastGapOffset registers i) := by
              calc
                shifted = (shifted.move (orient growth .right)).move
                    (orient growth .left) := by
                  funext position
                  cases growth <;>
                    simp [orient, FullTM0.Tape.move]
                _ = (atLogical growth coreTape
                    (boundaryOffset registers i.succ)).move
                      (orient growth .left) := by rw [hcenter]
                _ = atLogical growth coreTape
                    (lastGapOffset registers i) := by
                  rw [show boundaryOffset registers i.succ =
                      lastGapOffset registers i + 1 by
                    simp [lastGapOffset, boundaryOffset,
                      CounterLayout.boundaryPos_succ]]
                  simp only [orient_eq_orientDirection]
                  rw [atLogical_move_left]
            exact lowerBoundary_inwardAgreement_of_shiftedUpper hcore hread
              gap holdUpper terminal.blank (fun back hback =>
                terminal.ahead back hback) hclearedCanonical
          · have hupperStrict : (i.succ : Nat) < (endpoint : Nat) := by
              have hle := tail.source_le
              have hne : (i.succ : Nat) ≠ (endpoint : Nat) := by
                intro heq
                apply hterminal
                exact Fin.ext heq.symm
              omega
            have hupperAgreement := ih hupperStrict hupperRead restTrace
              terminal hcenter
            exact lowerBoundary_inwardAgreement_of_upperAgreement hcore hread
              gap holdUpper hupperAgreement

theorem descendingTo_last_le
    {current last : Fin 5} {labels : List (Fin 5)}
    (schedule : DescendingTo current labels last) :
    (last : Nat) ≤ (current : Nat) := by
  induction schedule with
  | done => simp
  | step i _ ih =>
      exact ih.trans (show (i.castSucc : Nat) ≤ (i.succ : Nat) by simp)

theorem descendingTo_eq_nil_of_same
    {current : Fin 5} {labels : List (Fin 5)}
    (schedule : DescendingTo current labels current) : labels = [] := by
  cases schedule with
  | done => rfl
  | step i tail =>
      have hle := descendingTo_last_le tail
      have hstep : (i.succ : Nat) = (i.castSucc : Nat) + 1 := by simp
      omega

theorem descendingTo_uncons_of_le_aux
    {current : Fin 5} {labels : List (Fin 5)} {last : Fin 5}
    (schedule : DescendingTo current labels last) (lower : Fin 4)
    (hcurrent : current = lower.succ)
    (hlast : (last : Nat) ≤ (lower : Nat)) :
    ∃ remaining, labels = lower.castSucc :: remaining ∧
      DescendingTo lower.castSucc remaining last := by
  cases schedule with
  | done label =>
      have hle : (lower.succ : Nat) ≤ (lower : Nat) := by
        simpa [hcurrent] using hlast
      simp at hle
  | step i tail =>
      have hi : i = lower := by
        apply Fin.ext
        have heq := congrArg Fin.val hcurrent
        simpa using heq
      subst i
      exact ⟨_, rfl, tail⟩

theorem descendingTo_uncons_of_le
    (lower : Fin 4) {labels : List (Fin 5)} {last : Fin 5}
    (schedule : DescendingTo lower.succ labels last)
    (hlast : (last : Nat) ≤ (lower : Nat)) :
    ∃ remaining, labels = lower.castSucc :: remaining ∧
      DescendingTo lower.castSucc remaining last :=
  descendingTo_uncons_of_le_aux schedule lower rfl hlast

/-- Pair a retained outward validation route with the reverse prefix of a
descending increment schedule.  The result stops at the route's source
boundary and retains the unconsumed lower shifts. -/
theorem alignOutwardRoute
    {growth : Turing.Dir} {source last : Fin 5}
    {route : List MarkerValidation.Leg} {labels : List (Fin 5)}
    (hroute : ToFour source route)
    {originalStart routeFinish shiftedStart shiftFinish :
      FullTM0.Tape (Symbol numTags)}
    (originalRead : originalStart.read = boundarySymbol source)
    (routeTrace : CounterControlRouteSuffixMortality.RouteTailGaps growth
      route originalStart routeFinish)
    (initial : ShiftedAgainst (orient growth .left) 4
      shiftedStart routeFinish)
    (shiftTrace : ShiftTailGaps (orient growth .left) labels
      shiftedStart shiftFinish)
    (schedule : DescendingTo 4 labels last)
    (hlast : (last : Nat) ≤ (source : Nat)) :
    ∃ shifted remaining,
      ShiftedAgainst (orient growth .left) source shifted originalStart ∧
      ShiftTailGaps (orient growth .left) remaining shifted shiftFinish ∧
      DescendingTo source remaining last := by
  induction hroute generalizing originalStart routeFinish shiftedStart labels with
  | four =>
      cases routeTrace
      exact ⟨shiftedStart, labels, initial, shiftTrace, schedule⟩
  | step i tail ih =>
      cases routeTrace with
      | cons _ _ originalStart routeFinish trace =>
          rcases routeGaps_uncons growth ⟨i.succ, .right⟩ _ _ _ trace with
            ⟨routeDistance, routeGap, remainingRoute⟩
          let found :=
            ((originalStart.move (orient growth .right)).moveN
              (orient growth .right) routeDistance)
          have foundRead : found.read = boundarySymbol i.succ := by
            change (Target.boundary i.succ).Matches found.read
            simpa [found, FullTM0.Tape.read_moveN] using routeGap.marked
          have hstepLe : (i.castSucc : Nat) ≤ (i.succ : Nat) := by
            simp
          have hlastUpper : (last : Nat) ≤ (i.succ : Nat) :=
            hlast.trans hstepLe
          rcases ih foundRead remainingRoute initial shiftTrace schedule
              hlastUpper with
            ⟨shiftedUpper, upperRemaining, upperAgreement, upperTrace,
              upperSchedule⟩
          rcases descendingTo_uncons_of_le i upperSchedule hlast with
            ⟨lowerRemaining, hupperRemaining, lowerSchedule⟩
          rw [hupperRemaining] at upperTrace
          cases upperTrace with
          | cons _ _ _ shiftDistance shiftGap shiftPositive _ lowerTrace =>
              let shiftedLower := shiftStepTape (orient growth .left)
                shiftedUpper shiftDistance i.castSucc
              have lowerAgreement : ShiftedAgainst (orient growth .left)
                  i.castSucc shiftedLower originalStart :=
                shiftedAgainst_retreat upperAgreement originalRead routeGap
                  shiftGap shiftPositive
              exact ⟨shiftedLower, lowerRemaining, lowerAgreement,
                lowerTrace, lowerSchedule⟩

/-- The first successful boundary-`4` shift agrees on its whole inward ray
with the boundary-`4` tape delivered by validation. -/
theorem firstIncrementAgreement
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags)) :
    ShiftedAgainst (orient growth .left) 4
      (shiftStepTape (orient growth .left)
        (T.move (orient growth .right)) 1 4) T := by
  refine ⟨CounterControlGuardedDecrementPositiveEmbedding.shiftStepTape_read_blank
    _ _ _ _, ?_, ?_⟩
  · exact CounterControlGuardedShiftEmbedding.shiftStepTape_destination
      _ _ _ _
  · intro k hk
    rw [CounterControlGuardedDecrementPositiveEmbedding.shiftStepTape_ahead
      _ _ _ _ k hk]
    have hrestore :
        (T.move (orient growth .right)).moveN (orient growth .left) 1 = T := by
      funext position
      cases growth <;>
        simp [orient, FullTM0.Tape.move, FullTM0.Tape.moveN,
          FullTM0.Tape.offset]
    rw [hrestore]

/-- A position witness for the selected immediate shift is necessarily the
head of the compiled schedule. -/
theorem immediateIncrementShift_position
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4)
    (position : IncrementShiftPosition growth source bodySearchBase true
      (MarkerShift.incrementOrder register)
      (immediateIncrementShift base c current growth source next register
        hrule hread).selectedRaw) :
    position.before = [] ∧ position.current = 4 ∧
      position.remaining = incrementRemaining register := by
  have haddress := congrArg RawCommand.address position.raw_eq
  simp only [immediateIncrementShift_selectedRaw] at haddress
  simp [firstIncrementRaw, RawCommand.address] at haddress
  have hbefore : position.before = [] := haddress
  have hlabels := position.labels_eq
  rw [hbefore] at hlabels
  cases register <;>
    simp [MarkerShift.incrementOrder, incrementRemaining] at hlabels ⊢ <;>
    aesop

/-- A blank outward destination turns the immediate first shift into the
guarded form consumed by the generic schedule API. -/
def guardedImmediateIncrement
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4)
    (hblank : (current.foundTape.move (orient growth .right)).read =
      blankSymbol) : GuardedSearch base c := by
  let shift := immediateIncrementShift base c current growth source next
    register hrule hread
  refine ⟨shift, ?_⟩
  change (shift.outer.move
    (NestingMachine.opposite shift.direction)).read = blankSymbol
  have hdirection := immediateIncrementShift_direction base c current growth
    source next register hrule hread
  have houter := immediateIncrementShift_outer base c current growth source
    next register hrule hread
  rw [hdirection, houter]
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  rw [hopposite]
  exact hblank

@[simp] theorem guardedImmediateIncrement_current
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hread : current.foundTape.read = boundarySymbol 4)
    (hblank : (current.foundTape.move (orient growth .right)).read =
      blankSymbol) :
    (guardedImmediateIncrement base c current growth source next register
      hrule hread hblank).current =
      immediateIncrementShift base c current growth source next register
        hrule hread := by
  rfl

theorem guardedImmediateIncrement_shiftedParentBacking
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (hraw : current.selectedRaw = .boundaryNavigation
      ⟨growth, source, 7⟩ 4 .right
        (bodyEntry growth source (.increment register next)) .preserve)
    (hread : current.foundTape.read = boundarySymbol 4)
    (hblank : (current.foundTape.move (orient growth .right)).read =
      blankSymbol) (expected : Fin 5) :
    (guardedImmediateIncrement base c current growth source next register
      hrule hread hblank).shiftedParentBacking expected =
      shiftStepTape (orient growth .left)
        ((current.outer.moveN (orient growth .right) current.distance).move
          (orient growth .right)) 1 expected := by
  let shift := immediateIncrementShift base c current growth source next
    register hrule hread
  let guarded := guardedImmediateIncrement base c current growth source next
    register hrule hread hblank
  have hshiftDirection : shift.direction = orient growth .left :=
    immediateIncrementShift_direction base c current growth source next
      register hrule hread
  have hfound : current.foundTape =
      current.outer.moveN (orient growth .right) current.distance := by
    simp [GenuineSearch.foundTape,
      outwardFour_increment_direction current growth source next register
        hraw]
  have hopposite : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  unfold GuardedSearch.shiftedParentBacking GuardedSearch.parentOuter
  change shiftStepTape guarded.direction
      ((guarded.current.outer.move
        (NestingMachine.opposite guarded.direction)))
      (guarded.current.distance + 1) expected = _
  rw [show guarded.direction = shift.direction by rfl]
  rw [show guarded.current = shift by rfl]
  rw [hshiftDirection, hopposite]
  dsimp [shift]
  simp only [immediateIncrementShift_distance,
    immediateIncrementShift_outer, Nat.zero_add]
  rw [hfound]

/-- Clearing boundary `4`, moving it outward, and returning to its old cell
does not disturb any cell of the old inward blank gap.  The returned source
cell itself is newly blank, so the statement includes `back = 0`. -/
theorem firstShift_reverse_blank
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance back : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary (4 : Fin 5)).Matches outer direction distance)
    (hback : back ≤ distance) :
    (((shiftStepTape (NestingMachine.opposite direction)
        ((outer.moveN direction distance).move direction) 1 4).moveN
      (NestingMachine.opposite direction) back).read) = blankSymbol := by
  cases back with
  | zero =>
      cases direction <;>
        simp [shiftStepTape, NestingMachine.opposite,
          FullTM0.Tape.read, FullTM0.Tape.move,
          FullTM0.Tape.moveN, FullTM0.Tape.write]
  | succ back =>
      have hdistance : 0 < distance := by omega
      let index := distance - (back + 1)
      have hindex : index < distance := by
        dsimp [index]
        omega
      have hblank := hgap.blank hindex
      cases direction <;>
        simp [shiftStepTape, NestingMachine.opposite,
          FullTM0.Tape.read, FullTM0.Tape.move,
          FullTM0.Tape.moveN, FullTM0.Tape.offset,
          FullTM0.Tape.write, index] at hblank ⊢ <;>
        split_ifs <;> try omega
      all_goals
        rw [← hblank]
        apply congrArg outer
        omega

/-- Looking inward from the endpoint of an outward exact gap reads blank
at every positive distance through the old origin. -/
theorem outwardFound_reverse_blank
    (direction : Turing.Dir)
    (outer : FullTM0.Tape (Symbol numTags)) (distance back : Nat)
    (target : Fin 5)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary target).Matches outer direction distance)
    (hpositive : 0 < back) (hback : back ≤ distance) :
    (((outer.moveN direction distance).moveN
      (NestingMachine.opposite direction) back).read) = blankSymbol := by
  let index := distance - back
  have hindex : index < distance := by
    dsimp [index]
    omega
  have hblank := hgap.blank hindex
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.read,
      FullTM0.Tape.moveN, FullTM0.Tape.offset, index] at hblank ⊢ <;>
    rw [← hblank] <;> congr 1 <;> omega

/-- The first remaining search of a non-clock increment is farther than the
old final-validation gap, and canonical recovery places that whole search
inside the reconstructed layout. -/
theorem outwardGap_lt_layoutEnd_of_incrementTail
    (growth : Turing.Dir) (i : Fin 4)
    (start finish coreTape : FullTM0.Tape (Symbol numTags))
    (oldDistance : Nat) (remaining : List (Fin 5)) (last : Fin 5)
    (registers : Registers)
    (trace : ShiftTailGaps (orient growth .left)
      (i.castSucc :: remaining) start finish)
    (schedule : DescendingTo i.castSucc remaining last)
    (hstartRead : (start.move (orient growth .right)).read =
      boundarySymbol i.succ)
    (holdBlank : ∀ back ≤ oldDistance,
      (start.moveN (orient growth .left) back).read = blankSymbol)
    (hcore : CoreRepresents registers growth coreTape)
    (hfinish : finish.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers last)) :
    oldDistance < layoutEnd registers := by
  cases trace with
  | cons _ _ _ distance gap positive _ tail =>
      let shifted := shiftStepTape (orient growth .left) start distance
        i.castSucc
      have hopposite : NestingMachine.opposite (orient growth .left) =
          orient growth .right := by
        cases growth <;> rfl
      have hshiftedRead :
          (shifted.move (orient growth .right)).read =
            boundarySymbol i.castSucc := by
        have hread :=
          CounterControlGuardedShiftEmbedding.shiftStepTape_destination
            (orient growth .left) start distance i.castSucc
        rw [hopposite] at hread
        simpa [shifted] using hread
      rcases descendingShift_canonicalBackwardGeometry schedule tail
          hshiftedRead hcore hfinish with ⟨suffix⟩
      have hsource :
          (start.move (NestingMachine.opposite
            (orient growth .left))).read = boundarySymbol i.succ := by
        rw [hopposite]
        exact hstartRead
      have hreverse := shiftStepTape_reverseGap (orient growth .left)
        start distance i.castSucc i.succ gap positive hsource
      have hcanonical : SearchGap
          (fun symbol => symbol = blankSymbol)
          (Target.boundary i.succ).Matches
          ((shifted.move (orient growth .right)).move
            (orient growth .right))
          (orient growth .right) (RegisterLayout.values registers i) := by
        constructor
        · intro k hk
          have hahead := suffix.ahead (k + 1)
          have hcoordinate : boundaryOffset registers i.castSucc +
              (k + 1) = firstGapOffset registers i + k := by
            simp [boundaryOffset, firstGapOffset]
            omega
          have hcoordinateInt :
              (boundaryOffset registers i.castSucc : Int) + (k + 1) =
                firstGapOffset registers i + k := by
            exact_mod_cast hcoordinate
          change (((shifted.move (orient growth .right)).moveN
            (orient growth .right) (k + 1)).read) = _ at hahead
          have hahead' :
              (((shifted.move (orient growth .right)).moveN
                (orient growth .right) (k + 1)).read) =
                  logicalTape growth coreTape
                    (firstGapOffset registers i + k) := by
            calc
              _ = logicalTape growth coreTape
                  ((boundaryOffset registers i.castSucc : Int) +
                    (k + 1)) := hahead
              _ = logicalTape growth coreTape
                  (firstGapOffset registers i + k) := by
                    congr 1
          have hblankRead :
              ((((shifted.move (orient growth .right)).move
                (orient growth .right)).moveN
                  (orient growth .right) k).read) = blankSymbol := by
            calc
              _ = (((shifted.move (orient growth .right)).moveN
                    (orient growth .right) (k + 1)).read) := by
                      rw [FullTM0.Tape.move_moveN]
              _ = logicalTape growth coreTape
                    (firstGapOffset registers i + k) := hahead'
              _ = blankSymbol := hcore.gap_blank i k hk
          simpa only [FullTM0.Tape.read_moveN] using hblankRead
        · have hahead := suffix.ahead
              (RegisterLayout.values registers i + 1)
          have hcoordinate : boundaryOffset registers i.castSucc +
              (RegisterLayout.values registers i + 1) =
                boundaryOffset registers i.succ := by
            simp [boundaryOffset, CounterLayout.boundaryPos_succ]
            omega
          change (((shifted.move (orient growth .right)).moveN
            (orient growth .right)
            (RegisterLayout.values registers i + 1)).read) = _ at hahead
          have hahead' :
              (((shifted.move (orient growth .right)).moveN
                (orient growth .right)
                (RegisterLayout.values registers i + 1)).read) =
                  logicalTape growth coreTape
                    (boundaryOffset registers i.succ) := by
            calc
              _ = logicalTape growth coreTape
                  ((boundaryOffset registers i.castSucc : Int) +
                    (RegisterLayout.values registers i + 1)) := hahead
              _ = logicalTape growth coreTape
                  (boundaryOffset registers i.succ) := by
                    congr 1
                    exact_mod_cast hcoordinate
          rw [hcore.boundary i.succ] at hahead'
          have hmarkedRead :
              ((((shifted.move (orient growth .right)).move
                (orient growth .right)).moveN (orient growth .right)
                (RegisterLayout.values registers i)).read) =
                  boundarySymbol i.succ := by
            calc
              _ = (((shifted.move (orient growth .right)).moveN
                    (orient growth .right)
                    (RegisterLayout.values registers i + 1)).read) := by
                      rw [FullTM0.Tape.move_moveN]
              _ = boundarySymbol i.succ := hahead'
          simpa [Target.Matches, FullTM0.Tape.read_moveN] using hmarkedRead
      have hreverse' : SearchGap (fun symbol => symbol = blankSymbol)
          (Target.boundary i.succ).Matches
          ((shifted.move (orient growth .right)).move
            (orient growth .right))
          (orient growth .right) (distance - 1) := by
        rw [hopposite] at hreverse
        simpa [shifted] using hreverse
      have hdistanceSub : distance - 1 =
          RegisterLayout.values registers i :=
        BoundedMarkerProgram.boundaryGap_distance_unique hreverse' hcanonical
      have hdistance : distance = RegisterLayout.values registers i + 1 := by
        omega
      have holdLt : oldDistance < distance := by
        by_contra hnot
        have hle : distance ≤ oldDistance := Nat.le_of_not_gt hnot
        have hblank := holdBlank distance hle
        have hmarked := gap.marked
        have hboundary :
            (start.moveN (orient growth .left) distance).read =
              boundarySymbol i.castSucc := by
          simpa [FullTM0.Tape.read_moveN, Target.Matches] using hmarked
        rw [hblank] at hboundary
        exact blankSymbol_ne_boundarySymbol i.castSucc hboundary
      rw [hdistance] at holdLt
      have hlayout : RegisterLayout.values registers i + 1 <
          layoutEnd registers := by
        fin_cases i <;>
          simp [layoutEnd, RegisterLayout.clockBoundary_eq,
            RegisterLayout.values] <;> omega
      exact holdLt.trans hlayout

/-- If the descending increment schedule reaches strictly inward of the
original validation boundary, pairing the common route prefix exposes the
first unconsumed shift.  Its destination must lie beyond the whole old
outward gap, while canonical backward geometry places it inside the
reconstructed layout. -/
theorem outwardSuffix_gap_lt_layoutEnd_of_lowerIncrementTail
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (suffix : Suffix current growth source (.increment register next))
    (last : Fin 5)
    (shiftStart shiftFinish coreTape : FullTM0.Tape (Symbol numTags))
    (labels : List (Fin 5)) (registers : Registers)
    (initial : ShiftedAgainst (orient growth .left) 4 shiftStart
      suffix.progress.suffix.finish)
    (shiftTrace : ShiftTailGaps (orient growth .left) labels shiftStart
      shiftFinish)
    (schedule : DescendingTo 4 labels last)
    (hlast : (last : Nat) ≤ (suffix.index : Nat))
    (hcore : CoreRepresents registers growth coreTape)
    (hfinish : shiftFinish.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers last)) :
    current.distance < layoutEnd registers := by
  have hlastSource : (last : Nat) ≤ (suffix.index.succ : Nat) := by
    exact hlast.trans (by simp)
  rcases alignOutwardRoute suffix.remaining_toFour suffix.current_read
      suffix.tailGaps initial shiftTrace schedule hlastSource with
    ⟨shifted, remaining, agreement, remainingTrace, remainingSchedule⟩
  rcases descendingTo_uncons_of_le suffix.index remainingSchedule hlast with
    ⟨later, hremaining, laterSchedule⟩
  rw [hremaining] at remainingTrace
  have hoppositeLeft : NestingMachine.opposite (orient growth .left) =
      orient growth .right := by
    cases growth <;> rfl
  have hoppositeRight : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have hstartRead :
      (shifted.move (orient growth .right)).read =
        boundarySymbol suffix.index.succ := by
    rw [← hoppositeLeft]
    exact agreement.destination
  have holdBlank : ∀ back ≤ current.distance,
      (shifted.moveN (orient growth .left) back).read = blankSymbol := by
    intro back hback
    cases back with
    | zero => simpa using agreement.blank
    | succ back =>
        have hagreement := agreement.ahead (back + 1) (by omega)
        have hold :
            (current.foundTape.moveN (orient growth .left)
              (back + 1)).read = blankSymbol := by
          rw [← suffix.current_foundTape, ← hoppositeRight]
          exact outwardFound_reverse_blank (orient growth .right)
            current.outer current.distance (back + 1) suffix.index.succ
            suffix.current_gap (by omega) hback
        exact hagreement.trans hold
  exact outwardGap_lt_layoutEnd_of_incrementTail growth suffix.index shifted
    shiftFinish coreTape current.distance later last registers remainingTrace
    laterSchedule hstartRead holdBlank hcore hfinish

/-- If the increment schedule stops strictly outside the original caller,
split validation at that terminal boundary.  The upper suffix pairs with all
increment shifts; reversing the unshifted lower prefix then identifies the
caller's whole inward ray with its canonical boundary. -/
theorem outwardSuffix_gap_lt_layoutEnd_of_upperIncrementTerminal
    {base : Nat} {c : Nat.Partrec.Code}
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (suffix : Suffix current growth source (.increment register next))
    (last : Fin 5)
    (shiftStart shiftFinish coreTape : FullTM0.Tape (Symbol numTags))
    (labels : List (Fin 5)) (registers : Registers)
    (initial : ShiftedAgainst (orient growth .left) 4 shiftStart
      suffix.progress.suffix.finish)
    (shiftTrace : ShiftTailGaps (orient growth .left) labels shiftStart
      shiftFinish)
    (schedule : DescendingTo 4 labels last)
    (hstrict : (suffix.index.succ : Nat) < (last : Nat))
    (hcore : CoreRepresents registers growth coreTape)
    (hfinish : shiftFinish.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers last)) :
    current.distance < layoutEnd registers := by
  have hle : (suffix.index.succ : Nat) ≤ (last : Nat) :=
    Nat.le_of_lt hstrict
  rcases CounterControlOutwardRoute.ToFour.splitAt
      suffix.remaining_toFour last hle with
    ⟨early, late, hroute, hearly, hlate⟩
  have hrouteTrace :
      CounterControlRouteSuffixMortality.RouteTailGaps growth
        (early ++ late) current.foundTape suffix.progress.suffix.finish := by
    rw [← hroute]
    exact suffix.tailGaps
  rcases hrouteTrace.split with
    ⟨middle, earlyTrace, lateTrace⟩
  have hmiddleRead : middle.read = boundarySymbol last :=
    hearly.finish_read suffix.current_read earlyTrace
  rcases alignOutwardRoute hlate hmiddleRead lateTrace initial shiftTrace
      schedule (Nat.le_refl (last : Nat)) with
    ⟨shifted, remaining, terminal, remainingTrace, remainingSchedule⟩
  have hremaining : remaining = [] :=
    descendingTo_eq_nil_of_same remainingSchedule
  rw [hremaining] at remainingTrace
  cases remainingTrace
  have inwardAgreement :=
    inwardAgreement_of_terminalIncrement hearly hstrict suffix.current_read
      earlyTrace terminal hcore hfinish
  apply distance_lt_layoutEnd_of_inwardAgreement hcore suffix.current_gap
    suffix.current_foundTape
  · intro back _
    exact inwardAgreement back
  · rfl

/-- When the increment schedule ends exactly at the original validation
boundary, the paired route leaves the old boundary cell blank and moves that
boundary one cell outward.  Thus the old gap becomes a canonical gap one
cell longer. -/
theorem outwardGap_lt_layoutEnd_of_terminalIncrementAgreement
    (growth : Turing.Dir) (index : Fin 4)
    (oldOuter oldFound shifted coreTape :
      FullTM0.Tape (Symbol numTags))
    (distance : Nat) (registers : Registers)
    (oldGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches oldOuter
      (orient growth .right) distance)
    (oldFound_eq : oldOuter.moveN (orient growth .right) distance =
      oldFound)
    (agreement : ShiftedAgainst (orient growth .left) index.succ shifted
      oldFound)
    (hcore : CoreRepresents registers growth coreTape)
    (hcenter : shifted.move (orient growth .right) =
      atLogical growth coreTape (boundaryOffset registers index.succ)) :
    distance < layoutEnd registers := by
  let newOuter := shifted.moveN (orient growth .left) distance
  have hopposite : NestingMachine.opposite (orient growth .right) =
      orient growth .left := by
    cases growth <;> rfl
  have newGap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary index.succ).Matches newOuter
      (orient growth .right) (distance + 1) := by
    constructor
    · intro forward hforward
      have hle : forward ≤ distance := by omega
      let back := distance - forward
      have hnew :
          (newOuter.moveN (orient growth .right) forward).read =
            (shifted.moveN (orient growth .left) back).read := by
        dsimp [newOuter, back]
        cases growth <;>
          simp [orient, FullTM0.Tape.read, FullTM0.Tape.moveN,
            FullTM0.Tape.offset] <;>
          congr 1 <;> omega
      rw [← FullTM0.Tape.read_moveN newOuter (orient growth .right) forward,
        hnew]
      by_cases hback : back = 0
      · simpa [hback] using agreement.blank
      · have hbackPositive : 0 < back := Nat.pos_of_ne_zero hback
        rw [agreement.ahead back hbackPositive]
        have hold :
            (oldFound.moveN (orient growth .left) back).read =
              (oldOuter.moveN (orient growth .right) forward).read := by
          rw [← oldFound_eq]
          dsimp [back]
          cases growth <;>
            simp [orient, FullTM0.Tape.read, FullTM0.Tape.moveN,
              FullTM0.Tape.offset] <;>
            congr 1 <;> omega
        rw [hold]
        simpa only [FullTM0.Tape.read_moveN] using oldGap.blank (by
          dsimp [back] at hback
          omega)
    · have hfound :
          newOuter.moveN (orient growth .right) (distance + 1) =
            shifted.move (orient growth .right) := by
        funext position
        cases growth <;>
          simp [newOuter, orient, FullTM0.Tape.move,
            FullTM0.Tape.moveN, FullTM0.Tape.offset] <;>
          congr 1 <;> omega
      rw [← FullTM0.Tape.read_moveN newOuter (orient growth .right)
        (distance + 1), hfound]
      change (shifted.move (orient growth .right)).read =
        boundarySymbol index.succ
      have hoppositeLeft : NestingMachine.opposite (orient growth .left) =
          orient growth .right := by
        cases growth <;> rfl
      rw [← hoppositeLeft]
      exact agreement.destination
  have hfound :
      newOuter.moveN (orient growth .right) (distance + 1) =
        atLogical growth coreTape (boundaryOffset registers index.succ) := by
    rw [show newOuter.moveN (orient growth .right) (distance + 1) =
        shifted.move (orient growth .right) by
      funext position
      cases growth <;>
        simp [newOuter, orient, FullTM0.Tape.move,
          FullTM0.Tape.moveN, FullTM0.Tape.offset] <;>
        congr 1 <;> omega]
    exact hcenter
  have hlong : distance + 1 < layoutEnd registers :=
    rightGap_distance_lt_layoutEnd hcore index (distance + 1) newGap hfound
  omega

/-- Uniform geometry of a completed increment schedule following an
arbitrary outward validation suffix.  The three cases compare the original
caller boundary with the increment's terminal shifted boundary. -/
theorem outwardSuffix_gap_lt_layoutEnd_of_completedIncrement
    (base : Nat) (c : Nat.Partrec.Code)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (suffix : Suffix current growth source (.increment register next))
    (hblank : (suffix.progress.suffix.finish.move
      (orient growth .right)).read = blankSymbol)
    (completed : IncrementShiftSuffixReached
      (guardedBodyIncrement base c growth source next register hrule
        suffix.progress.suffix.finish suffix.finish_read hblank)
      growth source register)
    (registers : Registers)
    (coreTape : FullTM0.Tape (Symbol numTags))
    (hcore : CoreRepresents registers growth coreTape)
    (hfinish : completed.finish.move (orient growth .right) =
      atLogical growth coreTape
        (boundaryOffset registers
          (MarkerSchedule.decrementStartBoundary register))) :
    current.distance < layoutEnd registers := by
  let guarded := guardedBodyIncrement base c growth source next register
    hrule suffix.progress.suffix.finish suffix.finish_read hblank
  have hposition : completed.position.before = [] ∧
      completed.position.current = 4 ∧
      completed.position.remaining = incrementRemaining register := by
    exact bodyIncrementShift_position base c growth source next register hrule
      suffix.progress.suffix.finish suffix.finish_read completed.position
  rcases hposition with ⟨hbefore, hcurrent, hremaining⟩
  have htrace : ShiftTailGaps (orient growth .left)
      (incrementRemaining register) (guarded.shiftedParentBacking 4)
      completed.finish := by
    simpa [guarded, hcurrent, hremaining] using completed.tailGaps
  have hschedule : DescendingTo 4 (incrementRemaining register)
      (MarkerSchedule.decrementStartBoundary register) := by
    have hschedule' := incrementShiftPosition_descendingTo completed.position
    simpa [hcurrent, hremaining] using hschedule'
  have hinitial : ShiftedAgainst (orient growth .left) 4
      (guarded.shiftedParentBacking 4)
      suffix.progress.suffix.finish := by
    rw [guardedBodyIncrement_shiftedParentBacking base c growth source next
      register hrule suffix.progress.suffix.finish suffix.finish_read hblank 4]
    exact firstIncrementAgreement growth suffix.progress.suffix.finish
  let last := MarkerSchedule.decrementStartBoundary register
  rcases lt_trichotomy (suffix.index.succ : Nat) (last : Nat) with
      hlower | hequal | hupper
  · exact outwardSuffix_gap_lt_layoutEnd_of_upperIncrementTerminal current
      growth source next register suffix last (guarded.shiftedParentBacking 4)
      completed.finish coreTape (incrementRemaining register) registers
      hinitial htrace hschedule hlower hcore (by simpa [last] using hfinish)
  · have hterminalEq : MarkerSchedule.decrementStartBoundary register =
        suffix.index.succ := by
      apply Fin.ext
      simpa [last] using hequal.symm
    rcases alignOutwardRoute suffix.remaining_toFour suffix.current_read
        suffix.tailGaps hinitial htrace hschedule (by rw [hterminalEq]) with
      ⟨shifted, remaining, agreement, remainingTrace,
        remainingSchedule⟩
    rw [hterminalEq] at remainingSchedule
    have hremainingNil : remaining = [] :=
      descendingTo_eq_nil_of_same remainingSchedule
    rw [hremainingNil] at remainingTrace
    cases remainingTrace
    exact outwardGap_lt_layoutEnd_of_terminalIncrementAgreement growth
      suffix.index current.outer current.foundTape completed.finish coreTape
      current.distance registers suffix.current_gap suffix.current_foundTape
      agreement hcore (by simpa [hterminalEq] using hfinish)
  · have hlast : (last : Nat) ≤ (suffix.index : Nat) := by
      have hstep : (suffix.index.succ : Nat) =
          (suffix.index : Nat) + 1 := by simp
      omega
    exact outwardSuffix_gap_lt_layoutEnd_of_lowerIncrementTail current growth
      source next register suffix last (guarded.shiftedParentBacking 4)
      completed.finish coreTape (incrementRemaining register) registers
      hinitial htrace hschedule hlast hcore (by simpa [last] using hfinish)

/-- A collision-free increment reached after any retained outward
validation suffix reconstructs an exact logical core, and the original
caller gap remains strictly inside that core. -/
theorem outwardSuffix_incrementSuccess_logical
    (base : Nat) (c : Nat.Partrec.Code)
    (hmortal : ¬ DominoProblem.FixedNonhalting c)
    (current : GenuineSearch base c)
    (growth : Turing.Dir) (source next : Nat) (register : Register)
    (hrule : (source, .increment register next) ∈
      GlobalSourceProgram.program)
    (suffix : Suffix current growth source (.increment register next))
    (hblank : (suffix.progress.suffix.finish.move
      (orient growth .right)).read = blankSymbol)
    (himmortal : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) (foundCfg current)) :
    ∃ core : CounterControlParentEmbedding.LogicalCore base c,
      FullTM0.Reaches (CounterControlNestingBridge.machine base c)
          (foundCfg current) core.cfg ∧
        current.distance < layoutEnd core.registers := by
  -- Enter the first increment shift at the completed validation tape, then
  -- expose its exact found generated search under immortality.
  let T := suffix.progress.suffix.finish
  let shift := bodyIncrementShift base c growth source next register hrule T
    suffix.finish_read
  let guarded := guardedBodyIncrement base c growth source next register hrule
    T suffix.finish_read hblank
  have hentry : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) shift.cfg := by
    rw [bodyIncrementShift_cfg]
    simpa [T, bodyEntry, searchRef, CounterControlPlan.resolve] using
      suffix.reaches_bodyEntry
  have himmortalEntry : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c) shift.cfg :=
    FullTM0.ImmortalFrom.of_reaches himmortal hentry
  have hfoundEntry :=
    CounterControlParentContinuation.reaches_foundCfg_of_immortal
      shift himmortalEntry
  have hfound : FullTM0.Reaches
      (CounterControlNestingBridge.machine base c)
      (foundCfg current) (foundCfg guarded.current) := by
    change FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current) (foundCfg shift)
    exact hentry.trans hfoundEntry
  have himmortalFound : FullTM0.ImmortalFrom
      (CounterControlNestingBridge.machine base c)
      (foundCfg guarded.current) :=
    FullTM0.ImmortalFrom.of_reaches himmortal hfound
  have hcommand : guarded.selectedRaw ∈
      incrementShiftCommands growth source register := by
    change shift.selectedRaw ∈ incrementShiftCommands growth source register
    rw [bodyIncrementShift_selectedRaw]
    exact firstIncrementRaw_mem_increment growth source register
  rcases guarded.incrementShift_suffix_of_immortal base c hmortal growth
      source register next hrule hcommand himmortalFound with
    ⟨shiftSuffix⟩
  rcases incrementDirectCompletion base c guarded growth source register next
      hrule shiftSuffix with ⟨completion⟩
  -- Clock increments hand off directly to the next logical state; the other
  -- registers traverse a preserving recovery route.  Both endpoints provide
  -- the centered core needed by the common retained-gap comparison.
  cases completion with
  | logical direct hroute =>
      have hregister : register = .clock := by
        cases register <;>
          simp_all [AnchoredCounterGeometry.routeFromIncrement]
      subst register
      have hlogical := direct.reachesLogical_of_route_eq_nil hroute
      have himmortalLogical : FullTM0.ImmortalFrom
          (CounterControlNestingBridge.machine base c)
          ⟨logicalState base c growth next,
            incrementAfterShiftTape direct.suffix⟩ :=
        FullTM0.ImmortalFrom.of_reaches himmortalFound hlogical
      rcases
          CounterControlValidationRoundtrip.logical_reconstructs_coreTarget_fields_of_immortal
            base c hmortal growth next direct.target_lt
            (incrementAfterShiftTape direct.suffix) himmortalLogical with
        ⟨instruction, registers, coreTape, limit, target, _nextRule, hcore,
          hcoreBefore, hrunway, htarget, hcenter, _hbody⟩
      let represented : CoreTargetRepresents registers growth limit target
          coreTape := {
        toCorePrefixRepresents := {
          toCoreRepresents := hcore
          core_before_limit := hcoreBefore
          runway := hrunway }
        target_matches := htarget }
      let core : CounterControlParentEmbedding.LogicalCore base c := {
        growth := growth
        source := next
        source_lt := direct.target_lt
        registers := registers
        tape := coreTape
        limit := limit
        target := target
        represented := represented }
      have hreaches : FullTM0.Reaches
          (CounterControlNestingBridge.machine base c)
          (foundCfg guarded.current) core.cfg := by
        rw [hcenter] at hlogical
        simpa [core, CounterControlParentEmbedding.LogicalCore.cfg,
          CounterControlParentEmbedding.LogicalCore.frame,
          CounterControlParentEmbedding.LogicalCore.abstract,
          prefixLogicalCfg] using hlogical
      have hfinish : direct.suffix.finish.move (orient growth .right) =
          atLogical growth coreTape
            (boundaryOffset registers
              (MarkerSchedule.decrementStartBoundary .clock)) := by
        simpa [incrementAfterShiftTape,
          MarkerSchedule.decrementStartBoundary, boundaryOffset_four] using
          hcenter
      have hinside : current.distance < layoutEnd registers := by
        exact outwardSuffix_gap_lt_layoutEnd_of_completedIncrement base c
          current growth source next .clock hrule suffix hblank direct.suffix
          registers coreTape hcore hfinish
      exact ⟨core, hfound.trans hreaches, hinside⟩
  | recovery first rest handoff =>
      rcases incrementRecoveryCenteredEnd base c hmortal guarded
          himmortalFound growth source register next first rest handoff with
        ⟨centered⟩
      have hfinish : handoff.direct.suffix.finish.move
          (orient growth .right) =
          atLogical growth centered.core.tape
            (boundaryOffset centered.core.registers
              (MarkerSchedule.decrementStartBoundary register)) := by
        simpa [incrementAfterShiftTape] using centered.shift_center
      have hinside : current.distance <
          layoutEnd centered.core.registers := by
        exact outwardSuffix_gap_lt_layoutEnd_of_completedIncrement base c
          current growth source next register hrule suffix hblank
          handoff.direct.suffix centered.core.registers centered.core.tape
          centered.core_represents hfinish
      exact ⟨centered.core, hfound.trans centered.reaches, hinside⟩

end

end CounterControlGenuineValidationOutwardIncrement
end Hooper
end Kari
end LeanWang
