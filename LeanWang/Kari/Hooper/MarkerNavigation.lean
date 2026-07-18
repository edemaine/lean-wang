/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerSchedule

/-!
# Navigation between canonical marker boundaries

The arithmetic schedules in `MarkerSchedule` start and finish at precisely
specified cells of a canonical five-boundary tape.  This file records the
head geometry needed by the finite controller to navigate between those
cells.  Stepping off a boundary gives the appropriate first- or last-gap
tape; a labelled search then crosses exactly the adjacent register gap.  The
statements include zero-valued registers, where the search distance is zero
and the first cell after one boundary is already the next boundary.

The final section identifies the one-cell searches needed immediately after
an increment or decrement.  These are the endpoints from which a controller
can return to its common instruction anchor at boundary `4`.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerNavigation

open Turing CounterMachine
open MarkerSchedule

/-! ## Exact head positions around one gap -/

/-- Moving right from the left boundary of gap `i` centers the head on the
first cell of that gap.  When the register is zero, this is already its right
boundary. -/
theorem boundaryTape_move_right (registers : Registers) (i : Fin 4) :
    (boundaryTape registers i.castSucc).move .right =
      firstGapTape registers i := by
  funext position
  simp [boundaryTape, firstGapTape, MarkerTape.firstGapCellTape,
    CounterLayout.firstGapCellTape, MarkerMachine.recenter,
    MarkerTape.boundaryPosition]
  congr 2
  all_goals ring

/-- Moving left from the right boundary of gap `i` centers the head on the
last cell of that gap.  When the register is zero, this is already its left
boundary. -/
theorem boundaryTape_move_left (registers : Registers) (i : Fin 4) :
    (boundaryTape registers i.succ).move .left =
      lastGapTape registers i := by
  funext position
  simp [boundaryTape, lastGapTape, MarkerTape.lastGapCellTape,
    CounterLayout.lastGapCellTape, MarkerMachine.recenter,
    MarkerTape.boundaryPosition]
  congr 2
  all_goals ring

/-- From the first cell of a gap, one left move recovers its labelled left
boundary. -/
theorem firstGapTape_move_left (registers : Registers) (i : Fin 4) :
    (firstGapTape registers i).move .left =
      boundaryTape registers i.castSucc := by
  rw [← boundaryTape_move_right registers i]
  simp

/-- From the last cell of a gap, one right move recovers its labelled right
boundary. -/
theorem lastGapTape_move_right (registers : Registers) (i : Fin 4) :
    (lastGapTape registers i).move .right =
      boundaryTape registers i.succ := by
  rw [← boundaryTape_move_left registers i]
  simp

/-! ## Encoded labelled searches across adjacent gaps -/

/-- The encoded first-gap tape has exactly the blank run leading to the
adjacent right boundary.  This theorem also covers a zero gap. -/
theorem firstGapTape_search_right (registers : Registers) (i : Fin 4) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol i.succ)
      (firstGapTape registers i) .right
      (RegisterLayout.values registers i) := by
  have h := MarkerMachine.encodeTape_searchGap
    (MarkerTape.searchGap_right_label registers i)
  simpa [firstGapTape] using h

/-- The encoded last-gap tape has exactly the blank run leading to the
adjacent left boundary.  This theorem also covers a zero gap. -/
theorem lastGapTape_search_left (registers : Registers) (i : Fin 4) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol i.castSucc)
      (lastGapTape registers i) .left
      (RegisterLayout.values registers i) := by
  have h := MarkerMachine.encodeTape_searchGap
    (MarkerTape.searchGap_left_label registers i)
  simpa [lastGapTape] using h

/-- After crossing a gap from left to right, the tape is centered exactly on
its right boundary. -/
theorem firstGapTape_moveN_right (registers : Registers) (i : Fin 4) :
    (firstGapTape registers i).moveN .right
        (RegisterLayout.values registers i) =
      boundaryTape registers i.succ := by
  funext position
  simp [firstGapTape, boundaryTape, MarkerTape.firstGapCellTape,
    CounterLayout.firstGapCellTape, MarkerMachine.recenter,
    MarkerTape.boundaryPosition, FullTM0.Tape.offset_right]
  congr 2
  all_goals ring

/-- After crossing a gap from right to left, the tape is centered exactly on
its left boundary. -/
theorem lastGapTape_moveN_left (registers : Registers) (i : Fin 4) :
    (lastGapTape registers i).moveN .left
        (RegisterLayout.values registers i) =
      boundaryTape registers i.castSucc := by
  funext position
  simp [lastGapTape, boundaryTape, MarkerTape.lastGapCellTape,
    CounterLayout.lastGapCellTape, MarkerMachine.recenter,
    MarkerTape.boundaryPosition, FullTM0.Tape.offset_left]
  congr 2
  all_goals ring

/-- One right step followed by the adjacent labelled search navigates from
boundary `i` to boundary `i+1`, including when gap `i` is empty. -/
theorem boundaryTape_search_right (registers : Registers) (i : Fin 4) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol i.succ)
      ((boundaryTape registers i.castSucc).move .right) .right
      (RegisterLayout.values registers i) := by
  rw [boundaryTape_move_right]
  exact firstGapTape_search_right registers i

/-- One left step followed by the adjacent labelled search navigates from
boundary `i+1` to boundary `i`, including when gap `i` is empty. -/
theorem boundaryTape_search_left (registers : Registers) (i : Fin 4) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol i.castSucc)
      ((boundaryTape registers i.succ).move .left) .left
      (RegisterLayout.values registers i) := by
  rw [boundaryTape_move_left]
  exact lastGapTape_search_left registers i

/-! ## Schedule endpoints -/

/-- A positive gap's last cell is blank and its right boundary is exactly one
step away. -/
theorem lastGapTape_search_right_one (registers : Registers) (i : Fin 4)
    (hpositive : 0 < RegisterLayout.values registers i) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol i.succ)
      (lastGapTape registers i) .right 1 := by
  constructor
  · intro k hk
    have hkzero : k = 0 := by omega
    subst k
    exact (lastGapTape_search_left registers i).blank hpositive
  · change ((lastGapTape registers i).move .right).read =
      MarkerMachine.boundarySymbol i.succ
    rw [lastGapTape_move_right]
    simp [boundaryTape, FullTM0.Tape.read, MarkerMachine.recenter]

/-- An increment always leaves a nonempty selected gap.  Its old source cell
is blank, and the newly shifted selected boundary is one step to the right. -/
theorem incrementFinishTape_search_right_one (registers : Registers)
    (register : Register) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol
        (decrementStartBoundary register))
      (incrementFinishTape registers register) .right 1 := by
  cases register with
  | left =>
      simpa [incrementFinishTape, decrementStartBoundary,
        RegisterLayout.values, Registers.increment, Registers.set,
        Registers.get] using
        lastGapTape_search_right_one (registers.increment .left)
          (0 : Fin 4) (by simp [RegisterLayout.values, Registers.increment,
            Registers.set, Registers.get])
  | right =>
      simpa [incrementFinishTape, decrementStartBoundary,
        RegisterLayout.values, Registers.increment, Registers.set,
        Registers.get] using
        lastGapTape_search_right_one (registers.increment .right)
          (1 : Fin 4) (by simp [RegisterLayout.values, Registers.increment,
            Registers.set, Registers.get])
  | temp =>
      simpa [incrementFinishTape, decrementStartBoundary,
        RegisterLayout.values, Registers.increment, Registers.set,
        Registers.get] using
        lastGapTape_search_right_one (registers.increment .temp)
          (2 : Fin 4) (by simp [RegisterLayout.values, Registers.increment,
            Registers.set, Registers.get])
  | clock =>
      simpa [incrementFinishTape, decrementStartBoundary,
        RegisterLayout.values, Registers.increment, Registers.set,
        Registers.get] using
        lastGapTape_search_right_one (registers.increment .clock)
          (3 : Fin 4) (by simp [RegisterLayout.values, Registers.increment,
            Registers.set, Registers.get])

/-- The one step recognized above centers an incremented layout exactly on
the selected register's right boundary. -/
theorem incrementFinishTape_move_right (registers : Registers)
    (register : Register) :
    (incrementFinishTape registers register).move .right =
      boundaryTape (registers.increment register)
        (decrementStartBoundary register) := by
  cases register <;>
    simp only [incrementFinishTape, decrementStartBoundary] <;>
    apply lastGapTape_move_right

/-- The tape one cell to the right of the final boundary has a one-cell
leftward labelled search back to boundary `4`. -/
theorem boundaryFourRight_search_left_one (registers : Registers) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol 4)
      ((boundaryTape registers 4).move .right) .left 1 := by
  constructor
  · intro k hk
    have hkzero : k = 0 := by omega
    subst k
    change MarkerMachine.encodeSymbol
      (MarkerTape.canonicalTape registers
        (MarkerTape.boundaryPosition registers 4 + 1)) =
        MarkerMachine.blankSymbol
    rw [MarkerMachine.encodeSymbol_eq_blank_iff]
    rw [MarkerTape.canonicalTape_eq_blank_iff]
    intro j hj
    fin_cases j <;>
      simp [MarkerTape.boundaryPosition] at hj <;>
      omega
  · change (((boundaryTape registers 4).move .right).move .left).read =
      MarkerMachine.boundarySymbol 4
    simp [boundaryTape, FullTM0.Tape.read, MarkerMachine.recenter]

/-- The decrement schedule's exit cell is exactly one cell to the right of
boundary `4` in the resulting canonical layout. -/
theorem decrementFinishTape_eq_boundaryFour_move_right
    (registers : Registers) (register : Register) :
    decrementFinishTape registers register =
      (boundaryTape (registers.decrement register) 4).move .right := by
  funext position
  simp [decrementFinishTape, decrementBaseFinishTape, boundaryTape,
    MarkerMachine.recenter, MarkerTape.boundaryPosition,
    Registers.increment, Registers.set, Registers.get]
  congr 2
  all_goals ring

/-- Thus every completed positive decrement has an exact one-cell search
back to the common instruction anchor at boundary `4`. -/
theorem decrementFinishTape_search_left_one (registers : Registers)
    (register : Register) :
    SearchGap (fun a => a = MarkerMachine.blankSymbol)
      (fun a => a = MarkerMachine.boundarySymbol 4)
      (decrementFinishTape registers register) .left 1 := by
  rw [decrementFinishTape_eq_boundaryFour_move_right]
  exact boundaryFourRight_search_left_one (registers.decrement register)

/-- Moving left once from a decrement endpoint centers the resulting layout
exactly on its boundary `4` anchor. -/
theorem decrementFinishTape_move_left (registers : Registers)
    (register : Register) :
    (decrementFinishTape registers register).move .left =
      boundaryTape (registers.decrement register) 4 := by
  rw [decrementFinishTape_eq_boundaryFour_move_right]
  simp

end MarkerNavigation
end Hooper
end Kari
end LeanWang
