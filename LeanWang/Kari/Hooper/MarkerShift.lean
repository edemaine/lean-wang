/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerTape
import Mathlib.Tactic.FinCases

/-!
# Moving register-boundary markers

This file gives the tape-level effect of incrementing and decrementing one of
Hooper's four sparse registers.  The operations are deliberately stated on an
arbitrary `FullTM0.Tape MarkerTape.Symbol`: they are finite combinations of
absolute-coordinate writes, and so form the specification that a later TM0
reachability proof can realize by moving its head to the indicated cells.

An increment moves the suffix of boundaries after the selected gap one cell
right.  The boundaries are moved from right to left, so a marker never
overwrites an as-yet-unmoved marker.  A positive decrement performs the inverse
operation, moving the same suffix left to right.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace MarkerShift

open CounterMachine
open MarkerTape

noncomputable section

/-- Replace one absolute-coordinate cell of a full tape.  Unlike
`FullTM0.Tape.write`, this operation does not require the head to be at the
cell; a later machine implementation can realize it by moving to `position`,
writing, and returning. -/
def writeAt (T : FullTM0.Tape Symbol) (position : Int) (symbol : Symbol) :
    FullTM0.Tape Symbol :=
  fun i => if i = position then symbol else T i

@[simp]
theorem writeAt_same (T : FullTM0.Tape Symbol) (position : Int) (symbol : Symbol) :
    writeAt T position symbol position = symbol := by
  simp [writeAt]

@[simp]
theorem writeAt_of_ne (T : FullTM0.Tape Symbol) (position i : Int)
    (symbol : Symbol) (h : i ≠ position) :
    writeAt T position symbol i = T i := by
  simp [writeAt, h]

/-- Absolute coordinate zero is the currently scanned cell, so `writeAt` at
zero is exactly the primitive head-relative full-tape write. -/
@[simp]
theorem writeAt_zero (T : FullTM0.Tape Symbol) (symbol : Symbol) :
    writeAt T 0 symbol = T.write symbol := by
  funext i
  simp [writeAt, FullTM0.Tape.write]

/-- Move labelled boundary `j` one cell right from the supplied absolute
coordinate: clear its old cell, then write it at the adjacent cell. -/
def moveRightAt (T : FullTM0.Tape Symbol) (position : Int) (j : Fin 5) :
    FullTM0.Tape Symbol :=
  writeAt (writeAt T position .blank) (position + 1) (.boundary j)

/-- Move labelled boundary `j` one cell left from the supplied absolute
coordinate: clear its old cell, then write it at the adjacent cell. -/
def moveLeftAt (T : FullTM0.Tape Symbol) (position : Int) (j : Fin 5) :
    FullTM0.Tape Symbol :=
  writeAt (writeAt T position .blank) (position - 1) (.boundary j)

@[simp]
theorem moveRightAt_eq_boundary_iff (T : FullTM0.Tape Symbol) (source i : Int)
    (j k : Fin 5) :
    moveRightAt T source j i = .boundary k ↔
      (i = source + 1 ∧ j = k) ∨
        (i ≠ source + 1 ∧ i ≠ source ∧ T i = .boundary k) := by
  by_cases htarget : i = source + 1
  · simp [moveRightAt, writeAt, htarget]
  · by_cases hsource : i = source
    · simp [moveRightAt, writeAt, hsource]
    · simp [moveRightAt, writeAt, htarget, hsource]

@[simp]
theorem moveLeftAt_eq_boundary_iff (T : FullTM0.Tape Symbol) (source i : Int)
    (j k : Fin 5) :
    moveLeftAt T source j i = .boundary k ↔
      (i = source - 1 ∧ j = k) ∨
        (i ≠ source - 1 ∧ i ≠ source ∧ T i = .boundary k) := by
  by_cases htarget : i = source - 1
  · simp [moveLeftAt, writeAt, htarget]
  · by_cases hsource : i = source
    · have hne : source ≠ source - 1 := by omega
      simp [moveLeftAt, writeAt, hsource, hne]
    · simp [moveLeftAt, writeAt, htarget, hsource]

/-- Move a canonical boundary right, using its position in the original
layout. -/
def moveCanonicalRight (v : Registers) (T : FullTM0.Tape Symbol) (j : Fin 5) :
    FullTM0.Tape Symbol :=
  moveRightAt T (boundaryPosition v j) j

/-- Move a canonical boundary left, using its position in the original
layout. -/
def moveCanonicalLeft (v : Registers) (T : FullTM0.Tape Symbol) (j : Fin 5) :
    FullTM0.Tape Symbol :=
  moveLeftAt T (boundaryPosition v j) j

/-- Boundary labels moved by an increment, in the collision-free order from
the rightmost boundary down to the boundary immediately after the selected
register gap. -/
def incrementOrder : Register → List (Fin 5)
  | .left => [4, 3, 2, 1]
  | .right => [4, 3, 2]
  | .temp => [4, 3]
  | .clock => [4]

/-- Boundary labels moved by a positive decrement, in the collision-free
order from the boundary immediately after the selected gap to the rightmost
boundary. -/
def decrementOrder : Register → List (Fin 5)
  | .left => [1, 2, 3, 4]
  | .right => [2, 3, 4]
  | .temp => [3, 4]
  | .clock => [4]

/-- Tape transformation implementing one register increment. -/
def incrementTape (v : Registers) (r : Register) (T : FullTM0.Tape Symbol) :
    FullTM0.Tape Symbol :=
  (incrementOrder r).foldl (moveCanonicalRight v) T

/-- Tape transformation implementing the positive branch of one register
decrement.  Its canonical-tape theorem below assumes that the selected
register is nonzero. -/
def decrementTape (v : Registers) (r : Register) (T : FullTM0.Tape Symbol) :
    FullTM0.Tape Symbol :=
  (decrementOrder r).foldl (moveCanonicalLeft v) T

/-- Two marker tapes are equal if every labelled boundary has the same
occurrence predicate on both tapes. -/
theorem tape_ext_boundary {T U : FullTM0.Tape Symbol}
    (h : ∀ position j, T position = .boundary j ↔ U position = .boundary j) :
    T = U := by
  funext position
  have hp := h position
  cases hT : T position with
  | blank =>
      cases hU : U position with
      | blank => rfl
      | boundary j =>
          have hcontra : T position = .boundary j := (hp j).mpr hU
          simp [hT] at hcontra
  | boundary j =>
      have hUj : U position = .boundary j := (hp j).mp hT
      simpa [hT] using hUj.symm

/-- Moving the suffix of a canonical marker tape right realizes named-register
increment exactly. -/
theorem incrementTape_canonical (v : Registers) (r : Register) :
    incrementTape v r (canonicalTape v) = canonicalTape (v.increment r) := by
  apply tape_ext_boundary
  intro position j
  cases r <;> fin_cases j <;>
    simp [incrementTape, incrementOrder, moveCanonicalRight,
      canonicalTape_eq_boundary_iff,
      Registers.increment, Registers.set, Registers.get,
      RegisterLayout.startBoundary_eq, RegisterLayout.leftBoundary_eq,
      RegisterLayout.rightBoundary_eq, RegisterLayout.tempBoundary_eq,
      RegisterLayout.clockBoundary_eq] <;>
    omega

/-- Moving the suffix of a canonical marker tape left realizes a positive
named-register decrement exactly. -/
theorem decrementTape_canonical (v : Registers) (r : Register)
    (hr : 0 < v.get r) :
    decrementTape v r (canonicalTape v) = canonicalTape (v.decrement r) := by
  apply tape_ext_boundary
  intro position j
  cases r <;> fin_cases j <;>
    simp_all [decrementTape, decrementOrder, moveCanonicalLeft,
      canonicalTape_eq_boundary_iff,
      Registers.decrement, Registers.set, Registers.get,
      RegisterLayout.startBoundary_eq, RegisterLayout.leftBoundary_eq,
      RegisterLayout.rightBoundary_eq, RegisterLayout.tempBoundary_eq,
      RegisterLayout.clockBoundary_eq] <;>
    omega

end

end MarkerShift
end Hooper
end Kari
end LeanWang
