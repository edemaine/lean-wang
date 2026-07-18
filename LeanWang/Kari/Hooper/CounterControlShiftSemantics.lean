/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlCommandAt
import LeanWang.Kari.Hooper.CounterControlBridge

/-!
# Nearby marker-shift semantics for generated counter commands

This module connects a symbolic `RawCommand.markerShift` from the counter
controller to the exact head-relative execution of its compiled bounded
command.  The statements use logical coordinates, so they apply uniformly to
the right-growing and reflected left-growing copies of the counter program.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlShiftSemantics

open Turing
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry
open CounterControlPlan CounterControlCommandAt CounterControlBridge

noncomputable section

/-! ## Outward shifts used by increment -/

/-- A generated outward marker shift whose target lies within the nesting
bound executes its successful branch.  The search starts `distance` cells to
the logical right of `source`, finds the expected marker at `source`, moves it
one cell right, and returns the head to `source`.

The theorem is command-oriented: the sole compiler-side assumption is that
the displayed raw command occurs in `rawCommands`. -/
theorem machine_reaches_incrementShift_near
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot source : Nat) (expected : Fin 5)
    (success : ControlRef) (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .left .right success
        (some .left) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches
      (atLogical growth T (source + distance))
      (OrientedMarkerTape.orientDirection growth .left) distance)
    (hnear : distance ≤ NestingMachine.bound (CanonicalInitializer.radius c))
    (hblank : logicalTape growth T (source + 1) = blankSymbol) :
    FullTM0.Reaches (machine base (CanonicalInitializer.radius c)
        (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, counterState, searchSlot⟩),
        atLogical growth T (source + distance)⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T source blankSymbol) (source + 1)
              (boundarySymbol expected)) source⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .left .right
      success (some .left) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .left,
      CounterControlPlan.orient growth .right⟩
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, counterState, searchSlot⟩)
      (.markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .left))
        (collision.map (resolve base c)))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hmove :
      (atLogical growth T (source + distance)).moveN
          (CounterControlPlan.orient growth .left) distance =
        atLogical growth T source := by
    simpa only [orient_eq_orientDirection] using
      atLogical_moveN_left growth T source distance
  have hblankPhysical :
      (((((atLogical growth T (source + distance)).moveN
          move.searchDirection distance).write blankSymbol).move
            move.shiftDirection).read = blankSymbol) := by
    rw [show move.searchDirection =
      CounterControlPlan.orient growth .left from rfl, hmove]
    change (((atLogical growth T source).write blankSymbol).move
      (CounterControlPlan.orient growth .right)).read = blankSymbol
    rw [atLogical_write]
    rw [show CounterControlPlan.orient growth .right =
      OrientedMarkerTape.orientDirection growth .right by
        exact orient_eq_orientDirection growth .right]
    rw [atLogical_move_right, atLogical_read]
    rw [writeLogical_of_ne growth T source (source + 1) blankSymbol (by omega)]
    exact hblank
  have hrun := machine_reaches_shift_success
    (coreTable base c) move (resolve base c success) (rawTag raw hraw)
      (some (CounterControlPlan.orient growth .left))
      (collision.map (resolve base c)) hat
      (atLogical growth T (source + distance)) distance
      (by simpa [move, orient_eq_orientDirection] using hgap) hnear
      hblankPhysical
  rw [show move.searchDirection =
    CounterControlPlan.orient growth .left from rfl, hmove] at hrun
  dsimp only [move] at hrun
  rw [orient_eq_orientDirection growth .right,
    orient_eq_orientDirection growth .left] at hrun
  rw [shiftRight_departLeft_atLogical] at hrun
  exact hrun

/-! ## Inward shifts used by conditional decrement -/

/-- A generated inward marker shift whose target lies within the nesting
bound executes its successful branch.  The equation `origin + distance =
destination + 1` names the cell immediately left of the found marker; that
cell is the destination of the shift.  After rewriting the marker, the
logical-right departure returns the head to its old coordinate. -/
theorem machine_reaches_decrementShift_near
    (base : Nat) (c : Nat.Partrec.Code) (growth : Turing.Dir)
    (counterState searchSlot origin destination distance : Nat)
    (expected : Fin 5) (success : ControlRef)
    (collision : Option ControlRef)
    (hraw : RawCommand.markerShift
      ⟨growth, counterState, searchSlot⟩ expected .right .left success
        (some .right) collision ∈ rawCommands)
    (T : FullTM0.Tape (Symbol numTags))
    (hposition : origin + distance = destination + 1)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches (atLogical growth T origin)
      (OrientedMarkerTape.orientDirection growth .right) distance)
    (hnear : distance ≤ NestingMachine.bound (CanonicalInitializer.radius c))
    (hblank : logicalTape growth T destination = blankSymbol) :
    FullTM0.Reaches (machine base (CanonicalInitializer.radius c)
        (commands base c) (coreTable base c))
      ⟨entryState (CanonicalInitializer.radius c)
          (searchState base c ⟨growth, counterState, searchSlot⟩),
        atLogical growth T origin⟩
      ⟨resolve base c success,
        atLogical growth
          (writeLogical growth
            (writeLogical growth T (destination + 1) blankSymbol) destination
              (boundarySymbol expected)) (destination + 1)⟩ := by
  let raw : RawCommand :=
    .markerShift ⟨growth, counterState, searchSlot⟩ expected .right .left
      success (some .right) collision
  let move : MarkerProgram.Move :=
    ⟨expected, CounterControlPlan.orient growth .right,
      CounterControlPlan.orient growth .left⟩
  have hatRaw := CommandAt.compileRawCommand base c raw hraw
  have hspec := compileRawCommand_spec base c raw hraw
  have hat : CommandAt (CanonicalInitializer.radius c) base
      (searchState base c ⟨growth, counterState, searchSlot⟩)
      (.markerShift move (resolve base c success) (rawTag raw hraw)
        (some (CounterControlPlan.orient growth .right))
        (collision.map (resolve base c)))
      (commands base c) := by
    rw [hspec] at hatRaw
    simpa [raw, move, compileRawAtTag, RawCommand.address] using hatRaw
  have hmove :
      (atLogical growth T origin).moveN
          (CounterControlPlan.orient growth .right) distance =
      atLogical growth T (destination + 1) := by
    rw [show CounterControlPlan.orient growth .right =
      OrientedMarkerTape.orientDirection growth .right by
        exact orient_eq_orientDirection growth .right]
    rw [atLogical_moveN_right, hposition]
  have hblankPhysical :
      (((((atLogical growth T origin).moveN move.searchDirection distance).write
          blankSymbol).move move.shiftDirection).read = blankSymbol) := by
    rw [show move.searchDirection =
      CounterControlPlan.orient growth .right from rfl, hmove]
    change (((atLogical growth T (destination + 1)).write blankSymbol).move
      (CounterControlPlan.orient growth .left)).read = blankSymbol
    rw [atLogical_write]
    rw [show CounterControlPlan.orient growth .left =
      OrientedMarkerTape.orientDirection growth .left by
        exact orient_eq_orientDirection growth .left]
    rw [atLogical_move_left, atLogical_read]
    rw [writeLogical_of_ne growth T (destination + 1) destination blankSymbol
      (by omega)]
    exact hblank
  have hrun := machine_reaches_shift_success
    (coreTable base c) move (resolve base c success) (rawTag raw hraw)
      (some (CounterControlPlan.orient growth .right))
      (collision.map (resolve base c)) hat
      (atLogical growth T origin) distance
      (by simpa [move, orient_eq_orientDirection] using hgap) hnear
      hblankPhysical
  rw [show move.searchDirection =
    CounterControlPlan.orient growth .right from rfl, hmove] at hrun
  dsimp only [move] at hrun
  rw [orient_eq_orientDirection growth .left,
    orient_eq_orientDirection growth .right] at hrun
  rw [shiftLeft_departRight_atLogical] at hrun
  exact hrun

end

end CounterControlShiftSemantics
end Hooper
end Kari
end LeanWang
