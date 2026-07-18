/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.BoundedMarkerContinuation
import LeanWang.Kari.Hooper.CounterControlPlan
import LeanWang.Kari.Hooper.FramedCounterGeometry

/-!
# Reusable execution bridges for the counter controller

This file records the small interface shared by the symbolic counter-control
plan, head-relative bounded-marker executions, and tag-centered framed tapes.
It identifies the two definitions of physical orientation, gives exact
recentring formulae for logical tape updates, and composes a bounded command's
entry-to-found execution with each concrete continuation.

The complete counter schedules and their frame-preservation proofs are kept
for a later semantic compiler module.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlBridge

open Turing
open BoundedMarkerProgram FramedMarkerTape FramedCounterGeometry

/-! ## The common physical orientation -/

/-- The counter-plan and framed-tape layers use the same interpretation of a
logical direction in either physical copy. -/
@[simp]
theorem orient_eq_orientDirection (growth logical : Turing.Dir) :
    CounterControlPlan.orient growth logical =
      OrientedMarkerTape.orientDirection growth logical := by
  cases growth <;> cases logical <;> rfl

/-! ## Recentring and logical writes -/

/-- Moving logically right from a recentered tape adds to its logical
coordinate, independently of the physical orientation. -/
theorem atLogical_moveN_right {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin distance : Nat) :
    (atLogical growth T origin).moveN
        (OrientedMarkerTape.orientDirection growth .right) distance =
      atLogical growth T (origin + distance) := by
  simpa only [atLogical,
    OrientedMarkerTape.orientDirection_growth_right] using
    FullTM0.Tape.moveN_add T growth origin distance

/-- Moving logically left by `distance` from logical coordinate
`origin + distance` returns to `origin`. -/
theorem atLogical_moveN_left {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin distance : Nat) :
    (atLogical growth T (origin + distance)).moveN
        (OrientedMarkerTape.orientDirection growth .left) distance =
      atLogical growth T origin := by
  cases growth with
  | left =>
      funext position
      simp [atLogical, OrientedMarkerTape.orientDirection,
        FullTM0.Tape.moveN, FullTM0.Tape.offset]
  | right =>
      funext position
      simp [atLogical, OrientedMarkerTape.orientDirection,
        FullTM0.Tape.moveN, FullTM0.Tape.offset]
      ring

/-- One logical right move advances a recentered tape by one cell. -/
@[simp]
theorem atLogical_move_right {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin : Nat) :
    (atLogical growth T origin).move
        (OrientedMarkerTape.orientDirection growth .right) =
      atLogical growth T (origin + 1) := by
  cases growth <;>
    funext position <;>
    simp [atLogical, OrientedMarkerTape.orientDirection,
      FullTM0.Tape.moveN, FullTM0.Tape.offset,
      FullTM0.Tape.move] <;>
    congr 1 <;> ring

/-- One logical left move from a successor coordinate returns to its
predecessor. -/
@[simp]
theorem atLogical_move_left {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin : Nat) :
    (atLogical growth T (origin + 1)).move
        (OrientedMarkerTape.orientDirection growth .left) =
      atLogical growth T origin := by
  cases growth <;>
    funext position <;>
    simp [atLogical, OrientedMarkerTape.orientDirection,
      FullTM0.Tape.moveN, FullTM0.Tape.offset,
      FullTM0.Tape.move]

/-- A head-relative write on a recentered tape is the corresponding absolute
write in logical coordinates, viewed from the same head position. -/
@[simp]
theorem atLogical_write {numTags : Nat} (growth : Turing.Dir)
    (T : FullTM0.Tape (Symbol numTags)) (origin : Nat)
    (written : Symbol numTags) :
    (atLogical growth T origin).write written =
      atLogical growth (writeLogical growth T origin written) origin := by
  funext position
  by_cases hposition : position = 0
  · subst position
    cases growth <;>
      simp [atLogical, writeLogical, physicalCoord,
        FullTM0.Tape.moveN, FullTM0.Tape.offset, FullTM0.Tape.write]
  · cases growth <;>
      simp [atLogical, writeLogical, physicalCoord,
        FullTM0.Tape.moveN, FullTM0.Tape.offset, FullTM0.Tape.write,
        hposition]

/-! ## Exact endpoints of the local tape actions -/

/-- Clear a logical source, shift its marker right, rewrite it, and depart
left.  The final head is back at the old source coordinate. -/
theorem shiftRight_departLeft_atLogical {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (source : Nat) (written : Symbol numTags) :
    (((((atLogical growth T source).write blankSymbol).move
        (OrientedMarkerTape.orientDirection growth .right)).write written).move
        (OrientedMarkerTape.orientDirection growth .left)) =
      atLogical growth
        (writeLogical growth
          (writeLogical growth T source blankSymbol) (source + 1) written)
        source := by
  rw [atLogical_write, atLogical_move_right, atLogical_write,
    atLogical_move_left]

/-- Clear a successor source, shift its marker left, rewrite it, and depart
right.  The final head is back at the old source coordinate. -/
theorem shiftLeft_departRight_atLogical {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (destination : Nat) (written : Symbol numTags) :
    (((((atLogical growth T (destination + 1)).write blankSymbol).move
        (OrientedMarkerTape.orientDirection growth .left)).write written).move
        (OrientedMarkerTape.orientDirection growth .right)) =
      atLogical growth
        (writeLogical growth
          (writeLogical growth T (destination + 1) blankSymbol)
          destination written)
        (destination + 1) := by
  rw [atLogical_write, atLogical_move_left, atLogical_write,
    atLogical_move_right]

/-- A right-shift collision clears the source and leaves the head on the
occupied destination without rewriting it. -/
theorem shiftRight_collision_atLogical {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (source : Nat) :
    ((atLogical growth T source).write blankSymbol).move
        (OrientedMarkerTape.orientDirection growth .right) =
      atLogical growth (writeLogical growth T source blankSymbol)
        (source + 1) := by
  rw [atLogical_write, atLogical_move_right]

/-- Erasing a marker at a successor coordinate and departing logically left
leaves the head at its predecessor. -/
theorem erase_departLeft_atLogical {numTags : Nat}
    (growth : Turing.Dir) (T : FullTM0.Tape (Symbol numTags))
    (destination : Nat) :
    ((atLogical growth T (destination + 1)).write blankSymbol).move
        (OrientedMarkerTape.orientDirection growth .left) =
      atLogical growth
        (writeLogical growth T (destination + 1) blankSymbol) destination := by
  rw [atLogical_write, atLogical_move_left]

/-! ## Whole-machine bounded-command wrappers -/

/-- A nearby navigation command executes from its command entry through the
found-state continuation, preserving the tape at the found target. -/
theorem machine_reaches_navigation {numTags : Nat}
    {base radius commandOffset : Nat}
    {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (target : Target numTags) (direction : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (hat : CommandAt radius base commandOffset
      (Command.navigateTarget target direction successState returnTag)
      commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      target.Matches T direction distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨successState, T.moveN direction distance⟩ := by
  cases target with
  | boundary expected =>
      have hfound := BoundedMarkerProgram.machine_reaches_found_native core hat
        T distance hgap hnear
      have hmatch : (Target.boundary expected).Matches
          (T.moveN direction distance).read := by
        simpa [FullTM0.Tape.read] using hgap.marked
      exact hfound.trans
        (BoundedMarkerContinuation.machine_reaches_navigation_native core
          (.boundary expected) direction successState returnTag hat
          (T.moveN direction distance) hmatch)
  | anyTag =>
      have hfound := BoundedMarkerProgram.machine_reaches_found_native core hat
        T distance hgap hnear
      have hmatch : (Target.anyTag : Target numTags).Matches
          (T.moveN direction distance).read := by
        simpa [FullTM0.Tape.read] using hgap.marked
      exact hfound.trans
        (BoundedMarkerContinuation.machine_reaches_navigation_native core
          .anyTag direction successState returnTag hat
          (T.moveN direction distance) hmatch)

/-- A nearby erase command executes from entry through its exact optional
departure endpoint. -/
theorem machine_reaches_erase {numTags : Nat}
    {base radius commandOffset : Nat}
    {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (expected : Fin 5) (direction : Turing.Dir)
    (successState : FiniteTM0.State) (returnTag : Fin numTags)
    (departure : Option Turing.Dir)
    (hat : CommandAt radius base commandOffset
      (Command.erase expected direction successState returnTag departure)
      commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary expected).Matches T direction distance)
    (hnear : distance ≤ NestingMachine.bound radius) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨successState, match departure with
        | none => (T.moveN direction distance).write blankSymbol
        | some departure =>
            ((T.moveN direction distance).write blankSymbol).move departure⟩ := by
  have hfound := BoundedMarkerProgram.machine_reaches_found_native core hat
    T distance hgap hnear
  have hread : (T.moveN direction distance).read =
      boundarySymbol expected := by
    simpa [FullTM0.Tape.read, Target.Matches] using hgap.marked
  exact hfound.trans
    (BoundedMarkerContinuation.machine_reaches_erase_native core expected
      direction successState returnTag departure hat
      (T.moveN direction distance) hread)

/-- A nearby collision-free marker shift executes from entry through its
exact optional-departure endpoint. -/
theorem machine_reaches_shift_success {numTags : Nat}
    {base radius commandOffset : Nat}
    {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (move : MarkerProgram.Move) (successState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (collisionState : Option FiniteTM0.State)
    (hat : CommandAt radius base commandOffset
      (Command.move move successState returnTag departure collisionState)
      commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary move.expected).Matches T move.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius)
    (hblank :
      ((((T.moveN move.searchDirection distance).write blankSymbol).move
          move.shiftDirection).read = blankSymbol)) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨successState, match departure with
        | none =>
            (((T.moveN move.searchDirection distance).write blankSymbol).move
              move.shiftDirection).write (boundarySymbol move.expected)
        | some departure =>
            ((((T.moveN move.searchDirection distance).write blankSymbol).move
              move.shiftDirection).write
                (boundarySymbol move.expected)).move departure⟩ := by
  have hfound := BoundedMarkerProgram.machine_reaches_found_native core hat
    T distance hgap hnear
  have hread : (T.moveN move.searchDirection distance).read =
      boundarySymbol move.expected := by
    simpa [FullTM0.Tape.read, Target.Matches] using hgap.marked
  exact hfound.trans
    (BoundedMarkerContinuation.machine_reaches_shift_success_native core move
      successState returnTag departure collisionState hat
      (T.moveN move.searchDirection distance) hread hblank)

/-- A nearby marker shift with an occupied destination executes from entry to
its collision state, preserving that destination symbol. -/
theorem machine_reaches_shift_collision {numTags : Nat}
    {base radius commandOffset : Nat}
    {commands : List (Command numTags)}
    (core : FiniteTM0.Table (AlphabetSize numTags))
    (move : MarkerProgram.Move)
    (successState collisionState : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (hat : CommandAt radius base commandOffset
      (Command.move move successState returnTag departure
        (some collisionState)) commands)
    (T : FullTM0.Tape (Symbol numTags)) (distance : Nat)
    (hgap : SearchGap (fun symbol => symbol = blankSymbol)
      (Target.boundary move.expected).Matches T move.searchDirection distance)
    (hnear : distance ≤ NestingMachine.bound radius)
    (hnonblank :
      ((((T.moveN move.searchDirection distance).write blankSymbol).move
          move.shiftDirection).read ≠ blankSymbol)) :
    FullTM0.Reaches (machine base radius commands core)
      ⟨entryState radius commandOffset, T⟩
      ⟨collisionState,
        ((T.moveN move.searchDirection distance).write blankSymbol).move
          move.shiftDirection⟩ := by
  have hfound := BoundedMarkerProgram.machine_reaches_found_native core hat
    T distance hgap hnear
  have hread : (T.moveN move.searchDirection distance).read =
      boundarySymbol move.expected := by
    simpa [FullTM0.Tape.read, Target.Matches] using hgap.marked
  exact hfound.trans
    (BoundedMarkerContinuation.machine_reaches_shift_collision_native core
      move successState collisionState returnTag departure hat
      (T.moveN move.searchDirection distance) hread hnonblank)

end CounterControlBridge
end Hooper
end Kari
end LeanWang
