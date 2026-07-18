/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanWang.Kari.Hooper.CounterControlResumedBacking
import LeanWang.Kari.Hooper.CounterControlParentContinuation

/-!
# Coordinates at the found state of a resumed parent caller

The shared return rule restarts a suspended search one cell into its old gap.
Its retained distance is therefore `limit - 1`.  When that search reaches its
target, the one-cell shift and the shortened distance recombine exactly: the
head is at logical coordinate `limit` of the recovered parent backing.

This file records that equality once, together with the target read and the
blank cell immediately behind the target.  The latter is especially useful
for generated marker shifts: whenever the shift direction reverses the
search direction, the resumed caller cannot take its collision branch.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterControlPrefixResume
namespace PrefixResumedSearch

open Turing
open BoundedMarkerProgram FramedMarkerTape
open CounterControlPlan CounterControlSearchSystem
open CounterControlParentContinuation
open CounterControlPrefixInstructionResolution

noncomputable section

private instance : Inhabited (Symbol numTags) :=
  ⟨blankSymbol⟩

variable {base : Nat} {c : Nat.Partrec.Code}
variable {frame : PrefixEnvelope}
variable {start : FullTM0.Cfg (Symbol numTags) FiniteTM0.State}

/-- Moving one step back after a positive run in one direction subtracts one
from that run, extensionally on a full tape. -/
private theorem moveN_move_opposite
    (T : FullTM0.Tape (Symbol numTags)) (direction : Turing.Dir)
    (distance : Nat) (hpositive : 0 < distance) :
    (T.moveN direction distance).move
        (NestingMachine.opposite direction) =
      T.moveN direction (distance - 1) := by
  funext position
  cases direction <;>
    simp [NestingMachine.opposite, FullTM0.Tape.moveN,
      FullTM0.Tape.offset, FullTM0.Tape.move] <;>
    congr 1 <;> omega

/-- A write at the head cannot affect the cell reached by a subsequent
one-cell move. -/
private theorem write_move_read
    (T : FullTM0.Tape (Symbol numTags)) (written : Symbol numTags)
    (direction : Turing.Dir) :
    ((T.write written).move direction).read = (T.move direction).read := by
  cases direction <;>
    simp [FullTM0.Tape.read, FullTM0.Tape.move, FullTM0.Tape.write]

/-- Tape centered at the original target of the suspended parent search. -/
def parentFoundTape
    (resumed : PrefixResumedSearch base c frame start) :
    FullTM0.Tape (Symbol numTags) :=
  atLogical frame.growth resumed.parentFrame.outer frame.limit

/-- The generic exact found configuration is the selected raw command's
found state, centered at coordinate `limit` of the recovered parent tape. -/
theorem foundCfg_eq_parentFound
    (resumed : PrefixResumedSearch base c frame start) :
    foundCfg resumed.next =
      ⟨foundState (CanonicalInitializer.radius c)
          (searchState base c resumed.selectedRaw.address),
        resumed.parentFoundTape⟩ := by
  have hlength : frame.limit - 1 + 1 = frame.limit := by
    have hpositive := resumed.limit_pos
    omega
  change
    (⟨foundState (CanonicalInitializer.radius c)
        (searchState base c
          (rawCommands.get resumed.next.search).address),
      resumed.next.outer.moveN
        (command base c resumed.next.search).searchDirection
        resumed.next.distance⟩ :
      FullTM0.Cfg (Symbol numTags) FiniteTM0.State) = _
  rw [resumed.next_outer_eq, resumed.direction_eq, resumed.distance_eq,
    FullTM0.Tape.move_moveN, hlength]
  rfl

/-- The exact found tape reads the prefix's retained first obstruction. -/
theorem parentFoundTape_matches
    (resumed : PrefixResumedSearch base c frame start) :
    frame.target.Matches resumed.parentFoundTape.read := by
  have hmark := resumed.parent_backedBy.searchGap.marked
  simpa [parentFoundTape, parentSpec,
    CounterControlRecoveredFrame.recoveredSpec, atLogical,
    FullTM0.Tape.read_moveN] using hmark

/-- Search-indexed form of the same exact found-target fact. -/
theorem selected_target_matches_parentFoundTape
    (resumed : PrefixResumedSearch base c frame start) :
    (command base c resumed.next.search).target.Matches
      resumed.parentFoundTape.read := by
  rw [resumed.selected_target_eq]
  exact resumed.parentFoundTape_matches

/-- Raw-command form of the exact found-target fact. -/
theorem selectedRaw_target_matches_parentFoundTape
    (resumed : PrefixResumedSearch base c frame start) :
    (CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
      resumed.selectedRaw_mem).target.Matches
        resumed.parentFoundTape.read := by
  rw [resumed.compileRawCommand_selectedRaw]
  exact resumed.selected_target_matches_parentFoundTape

/-- Moving one cell opposite the recovered search direction from its target
returns to coordinate `limit - 1` of the parent tape. -/
theorem parentFoundTape_move_opposite
    (resumed : PrefixResumedSearch base c frame start) :
    resumed.parentFoundTape.move
        (NestingMachine.opposite frame.growth) =
      atLogical frame.growth resumed.parentFrame.outer (frame.limit - 1) := by
  exact moveN_move_opposite resumed.parentFrame.outer frame.growth
    frame.limit resumed.limit_pos

/-- The cell immediately behind the found target, toward the resumed search
origin, is still one of the original blank gap cells. -/
theorem parentFoundTape_opposite_read
    (resumed : PrefixResumedSearch base c frame start) :
    (resumed.parentFoundTape.move
      (NestingMachine.opposite frame.growth)).read = blankSymbol := by
  rw [resumed.parentFoundTape_move_opposite]
  have hlt : frame.limit - 1 < frame.limit := by
    have hpositive := resumed.limit_pos
    omega
  have hblank := resumed.selectedRaw_originalGap.blank hlt
  simpa [atLogical, FullTM0.Tape.read_moveN] using hblank

/-- Clearing the found target does not change the neighboring cell behind
it.  Thus a marker shift which reverses the search direction sees blank. -/
theorem reverse_shift_destination_blank
    (resumed : PrefixResumedSearch base c frame start)
    (shiftDirection : Turing.Dir)
    (hreverse : shiftDirection = NestingMachine.opposite frame.growth) :
    ((resumed.parentFoundTape.write blankSymbol).move
      shiftDirection).read = blankSymbol := by
  subst shiftDirection
  have hneighbor := resumed.parentFoundTape_opposite_read
  rw [write_move_read]
  exact hneighbor

/-- A compiled marker shift whose physical shift reverses the resumed search
direction necessarily takes its success branch at this found state. -/
theorem markerShift_destination_blank
    (resumed : PrefixResumedSearch base c frame start)
    (move : MarkerProgram.Move) (success : FiniteTM0.State)
    (returnTag : Fin numTags) (departure : Option Turing.Dir)
    (collision : Option FiniteTM0.State)
    (_hcommand :
      CounterControlCommandAt.compileRawCommand base c resumed.selectedRaw
          resumed.selectedRaw_mem =
        .markerShift move success returnTag departure collision)
    (hreverse : move.shiftDirection = NestingMachine.opposite frame.growth) :
    ((resumed.parentFoundTape.write blankSymbol).move
      move.shiftDirection).read = blankSymbol := by
  exact resumed.reverse_shift_destination_blank move.shiftDirection hreverse

end

end PrefixResumedSearch
end CounterControlPrefixResume
end Hooper
end Kari
end LeanWang
