/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlGuardedSearch
import LeanWang.Kari.Hooper.CounterControlParentContinuation
import LeanWang.Kari.Hooper.CounterControlExactCommandContinuation
import LeanWang.Kari.Hooper.CounterControlRawCallerClassification

/-!
# Exact coordinates of a guarded generated search

This file is the command-facing interface to `GuardedSearch`.  It identifies
the selected raw command and its exact found tape, restores the parent
coordinate `distance + 1`, and proves that every selected generated marker
shift has a blank destination.  Consequently every guarded found command
continues through its ordinary success reference.

The API is independent of the instruction family containing the raw command,
so route, validation, cleanup, and marker-shift proofs can share it.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlGuardedSearch

open Turing
open BoundedMarkerProgram CounterControlPlan CounterControlSearchSystem
open CounterControlExactCommandContinuation
open CounterControlCommandContinuationMortality
open CounterControlGlobalUnnesting CounterControlParentContinuation

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

namespace GuardedSearch

variable {base : Nat} {c : Nat.Partrec.Code}

/-- The raw command selected by a guarded generated search. -/
def selectedRaw (current : GuardedSearch base c) : RawCommand :=
  rawCommands.get current.current.search

/-- The selected raw command belongs to the global generated command list. -/
theorem selectedRaw_mem (current : GuardedSearch base c) :
    current.selectedRaw ∈ rawCommands :=
  List.get_mem rawCommands current.current.search

/-- Re-enumerating the selected raw command recovers the packaged search. -/
@[simp] theorem rawTag_selectedRaw (current : GuardedSearch base c) :
    CounterControlCommandAt.rawTag current.selectedRaw
        current.selectedRaw_mem = current.current.search := by
  apply CounterControlCommandAt.rawTag_eq_of_get_eq
  rfl

/-- Command-oriented compilation agrees with the command stored in the
guarded genuine search. -/
@[simp] theorem compileRawCommand_selectedRaw
    (current : GuardedSearch base c) :
    CounterControlCommandAt.compileRawCommand base c current.selectedRaw
        current.selectedRaw_mem =
      command base c current.current.search := by
  unfold CounterControlCommandAt.compileRawCommand command
  rw [current.rawTag_selectedRaw]

/-- The physical search direction of the selected raw command. -/
theorem selectedRaw_direction_eq (current : GuardedSearch base c) :
    (CounterControlCommandAt.compileRawCommand base c current.selectedRaw
      current.selectedRaw_mem).searchDirection = current.direction := by
  rw [current.compileRawCommand_selectedRaw]
  rfl

/-- Tape centered at the exact target found by the guarded search. -/
def foundTape (current : GuardedSearch base c) :
    FullTM0.Tape (Symbol numTags) :=
  current.current.outer.moveN current.direction current.current.distance

/-- The found tape has the equivalent parent coordinate `distance + 1`. -/
theorem foundTape_eq_parentMoveN (current : GuardedSearch base c) :
    current.foundTape =
      current.parentOuter.moveN current.direction
        (current.current.distance + 1) := by
  exact current.moveN_distance_eq_parentMoveN

/-- The generic successful-search configuration is the selected raw
command's found state centered on `foundTape`. -/
theorem foundCfg_eq (current : GuardedSearch base c) :
    foundCfg current.current =
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c current.selectedRaw.address),
        current.foundTape⟩ := by
  rfl

/-- The selected compiled target matches the exact found tape. -/
theorem selectedRaw_target_matches_foundTape
    (current : GuardedSearch base c) :
    (CounterControlCommandAt.compileRawCommand base c current.selectedRaw
      current.selectedRaw_mem).target.Matches current.foundTape.read := by
  rw [current.compileRawCommand_selectedRaw]
  simpa [foundTape, direction, FullTM0.Tape.read_moveN] using
    current.current.gap.marked

private theorem moveN_succ_move_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) :
    (T.moveN direction (distance + 1)).move
        (NestingMachine.opposite direction) =
      T.moveN direction distance := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move]

private theorem write_move_read
    (T : FullTM0.Tape (Symbol numTags)) (written : Symbol numTags)
    (direction : Turing.Dir) :
    ((T.write written).move direction).read = (T.move direction).read := by
  cases direction <;>
    simp [FullTM0.Tape.read, FullTM0.Tape.move, FullTM0.Tape.write]

/-- The cell immediately behind the exact found target is blank.  This is
the last blank of the recovered parent gap; when the current distance is
zero it is exactly the one-cell guard. -/
theorem foundTape_opposite_read (current : GuardedSearch base c) :
    (current.foundTape.move
      (NestingMachine.opposite current.direction)).read = blankSymbol := by
  rw [current.foundTape_eq_parentMoveN,
    moveN_succ_move_opposite]
  have hblank := current.parentGap.blank
    (show current.current.distance < current.current.distance + 1 by omega)
  simpa [FullTM0.Tape.read_moveN] using hblank

/-- Clearing the found target cannot change its blank predecessor. -/
theorem reverse_shift_destination_blank
    (current : GuardedSearch base c) :
    ((current.foundTape.write blankSymbol).move
      (NestingMachine.opposite current.direction)).read = blankSymbol := by
  rw [write_move_read]
  exact current.foundTape_opposite_read

/-- Every generated marker shift selected by a guarded search has a free
destination at the exact found target. -/
theorem selectedRaw_destinationFree (current : GuardedSearch base c) :
    ¬ ShiftDestinationOccupied current.selectedRaw current.foundTape := by
  cases hselected : current.selectedRaw with
  | boundaryNavigation address expected direction success action =>
      simp [ShiftDestinationOccupied]
  | tagNavigation address direction success =>
      simp [ShiftDestinationOccupied]
  | markerShift address expected search shift success departure collision =>
      intro hoccupied
      have hmem : RawCommand.markerShift address expected search shift success
          departure collision ∈ rawCommands := by
        simpa [hselected] using current.selectedRaw_mem
      have hopposite :=
        CounterControlRawCallerClassification.markerShift_oriented_shift_eq_opposite_search
          address expected search shift success departure collision hmem
      have hsearch : orient address.growth search = current.direction := by
        have hdirection := current.selectedRaw_direction_eq
        rw [CounterControlCommandAt.compileRawCommand_searchDirection]
          at hdirection
        rw [hselected] at hdirection
        exact hdirection
      rw [hsearch] at hopposite
      change ((current.foundTape.write blankSymbol).move
        (orient address.growth shift)).read ≠ blankSymbol at hoccupied
      rw [hopposite] at hoccupied
      exact hoccupied current.reverse_shift_destination_blank

/-- Exact successful continuation of the selected guarded raw command. -/
theorem reaches_selectedRaw_success (current : GuardedSearch base c) :
    FullTM0.Reaches (CounterControlNestingBridge.machine base c)
      (foundCfg current.current)
      ⟨resolve base c (rawSuccessRef current.selectedRaw),
        exactSuccessTape current.selectedRaw current.foundTape⟩ := by
  have outcome := exact_found_continuation base c current.selectedRaw
    current.selectedRaw_mem current.foundTape
    current.selectedRaw_target_matches_foundTape
  have hrun := outcome.reachesSuccess_of_destinationFree
    current.selectedRaw_destinationFree
  rw [current.foundCfg_eq]
  exact hrun

end GuardedSearch

end


end CounterControlGuardedSearch
end Hooper
end Kari
end LeanWang
