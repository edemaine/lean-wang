/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.MarkerValidation
import LeanWang.Kari.Hooper.FramedMarkerTape

/-!
# Boundary-4 geometry for counter instructions

The concrete counter controller uses boundary `4` as its sole logical anchor.
This file identifies the finite navigation routes around the already verified
increment and positive-decrement schedules:

* a decrement first navigates left from boundary `4` to the boundary after
  its selected register;
* a completed increment takes one right step to that same boundary and then
  navigates right back to boundary `4`;
* a zero test steps left onto the preceding boundary and follows a slightly
  longer rightward route back to boundary `4`;
* a positive test steps left onto a blank and then right back to the starting
  boundary before running the decrement schedule.

All route proofs are exact and include zero-valued adjacent gaps.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace AnchoredCounterGeometry

open Turing CounterMachine
open MarkerSchedule
open FramedMarkerTape

private def leftLeg (target : Fin 5) : MarkerValidation.Leg :=
  ⟨target, .left⟩

private def rightLeg (target : Fin 5) : MarkerValidation.Leg :=
  ⟨target, .right⟩

/-! ## Boundary arithmetic -/

/-- Finite gap index corresponding to a named register. -/
def registerGap : Register → Fin 4
  | .left => 0
  | .right => 1
  | .temp => 2
  | .clock => 3

@[simp]
theorem registerGap_val (register : Register) :
    (registerGap register : Nat) = RegisterLayout.registerIndex register := by
  cases register <;> rfl

@[simp]
theorem registerGap_succ (register : Register) :
    (registerGap register).succ = decrementStartBoundary register := by
  cases register <;> rfl

@[simp] theorem values_registerGap (registers : Registers)
    (register : Register) :
    RegisterLayout.values registers (registerGap register) =
      registers.get register := by
  cases register <;> rfl

/-- The old source of an incremented boundary is the last cell of the
enlarged register gap. -/
theorem incrementSource_eq_lastGap (registers : Registers)
    (register : Register) :
    firstGapOffset (registers.increment register) (registerGap register) +
        registers.get register =
      boundaryOffset registers (decrementStartBoundary register) := by
  cases register <;>
    simp [registerGap, decrementStartBoundary, firstGapOffset,
      boundaryOffset, CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.set, Registers.get] <;> omega

/-- Each register value is bounded by the end of the complete marker layout. -/
theorem registerValue_lt_of_layoutEnd_lt (registers : Registers)
    (i : Fin 4) {limit : Nat} (h : layoutEnd registers < limit) :
    RegisterLayout.values registers i < limit := by
  fin_cases i <;>
    simp [RegisterLayout.values, layoutEnd,
      RegisterLayout.clockBoundary_eq] at h ⊢ <;> omega

/-- A strict upper bound on a complete marker layout is positive. -/
theorem limit_positive_of_layoutEnd_lt (registers : Registers)
    {limit : Nat} (h : layoutEnd registers < limit) : 0 < limit := by
  have hend : 0 < layoutEnd registers := by
    simp [layoutEnd, RegisterLayout.clockBoundary_eq]
  omega

/-- The first cell after an increment schedule is the corresponding boundary
in the incremented layout. -/
theorem incrementStartBoundary_add_one (registers : Registers)
    (register : Register) :
    boundaryOffset registers (decrementStartBoundary register) + 1 =
      boundaryOffset (registers.increment register)
        (decrementStartBoundary register) := by
  cases register <;>
    simp [decrementStartBoundary, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values,
      Registers.increment, Registers.set, Registers.get] <;> omega

/-- When the selected register is zero, stepping left from its final boundary
lands on the preceding boundary. -/
theorem zeroTest_predecessor (registers : Registers) (register : Register)
    (hzero : registers.get register = 0) :
    boundaryOffset registers (decrementStartBoundary register) - 1 =
      boundaryOffset registers (registerGap register).castSucc := by
  cases register <;>
    simp [Registers.get] at hzero <;>
    simp [decrementStartBoundary, registerGap, boundaryOffset,
      CounterLayout.boundaryPos, RegisterLayout.values, hzero]

/-- Arithmetic coordinate of the last blank cell in a positive selected
register gap. -/
theorem positiveTest_predecessor (registers : Registers)
    (register : Register) (hpositive : 0 < registers.get register) :
    firstGapOffset registers (registerGap register) +
        (registers.get register - 1) =
      boundaryOffset registers (decrementStartBoundary register) - 1 := by
  cases register <;>
    simp [Registers.get, decrementStartBoundary, registerGap,
      firstGapOffset, boundaryOffset, CounterLayout.boundaryPos,
      RegisterLayout.values] at hpositive ⊢ <;> omega

/-! ## Instruction navigation routes -/

/-- Route from boundary `4` to the boundary immediately after the selected
register. -/
def routeToDecrementStart : Register → List MarkerValidation.Leg
  | .left => [leftLeg 3, leftLeg 2, leftLeg 1]
  | .right => [leftLeg 3, leftLeg 2]
  | .temp => [leftLeg 3]
  | .clock => []

/-- Route from the boundary immediately after the selected register back to
boundary `4`.  This is used after an increment. -/
def routeFromIncrement : Register → List MarkerValidation.Leg
  | .left => [rightLeg 2, rightLeg 3, rightLeg 4]
  | .right => [rightLeg 3, rightLeg 4]
  | .temp => [rightLeg 4]
  | .clock => []

/-- Route used by the zero branch.  After the test's left step, the head is
on the boundary immediately before the selected gap. -/
def routeFromZero : Register → List MarkerValidation.Leg
  | .left => [rightLeg 1, rightLeg 2, rightLeg 3, rightLeg 4]
  | .right => [rightLeg 2, rightLeg 3, rightLeg 4]
  | .temp => [rightLeg 3, rightLeg 4]
  | .clock => [rightLeg 4]

theorem routeFromZero_ne_nil (register : Register) :
    routeFromZero register ≠ [] := by
  cases register <;> simp [routeFromZero]

/-! ## Route execution on canonical layouts -/

/-- The decrement-entry route reaches the selected boundary on a canonical
layout. -/
theorem routeToDecrementStart_executes (registers : Registers)
    (register : Register) :
    MarkerValidation.Executes (routeToDecrementStart register)
      (boundaryTape registers 4)
      (boundaryTape registers (decrementStartBoundary register)) := by
  cases register with
  | left =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.leftLeg_executes registers (3 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 2) _
        (MarkerValidation.leftLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 1) _
        (MarkerValidation.leftLeg_executes registers (1 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | right =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.leftLeg_executes registers (3 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 2) _
        (MarkerValidation.leftLeg_executes registers (2 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | temp =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.leftLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | clock => exact MarkerValidation.Executes.nil _

theorem routeFromIncrement_executes (registers : Registers)
    (register : Register) :
    MarkerValidation.Executes (routeFromIncrement register)
      (boundaryTape registers (decrementStartBoundary register))
      (boundaryTape registers 4) := by
  cases register with
  | left =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 2) _
        (MarkerValidation.rightLeg_executes registers (1 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.rightLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | right =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.rightLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | temp =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | clock => exact MarkerValidation.Executes.nil _

/-- After a completed increment, one right step and the finite recovery route
return to boundary `4` of the incremented layout. -/
theorem incrementRecovery_executes (registers : Registers)
    (register : Register) :
    MarkerValidation.Executes (routeFromIncrement register)
      ((incrementFinishTape registers register).move .right)
      (boundaryTape (registers.increment register) 4) := by
  rw [MarkerNavigation.incrementFinishTape_move_right]
  exact routeFromIncrement_executes (registers.increment register) register

theorem routeFromZero_executes (registers : Registers)
    (register : Register) :
    MarkerValidation.Executes (routeFromZero register)
      (boundaryTape registers (registerGap register).castSucc)
      (boundaryTape registers 4) := by
  cases register with
  | left =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 1) _
        (MarkerValidation.rightLeg_executes registers (0 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 2) _
        (MarkerValidation.rightLeg_executes registers (1 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.rightLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | right =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 2) _
        (MarkerValidation.rightLeg_executes registers (1 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.rightLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | temp =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 3) _
        (MarkerValidation.rightLeg_executes registers (2 : Fin 4))
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _
  | clock =>
      apply MarkerValidation.Executes.cons _ _ _
        (boundaryTape registers 4) _
        (MarkerValidation.rightLeg_executes registers (3 : Fin 4))
      exact MarkerValidation.Executes.nil _

/-- If the selected register is zero, the test's left step lands exactly on
the boundary immediately before that register gap. -/
theorem zeroTest_move_left (registers : Registers) (register : Register)
    (hzero : registers.get register = 0) :
    (boundaryTape registers (decrementStartBoundary register)).move .left =
      boundaryTape registers (registerGap register).castSucc := by
  have hvalue : RegisterLayout.values registers
      (registerGap register) = 0 := by
    cases register <;>
      simpa [RegisterLayout.values, Registers.get] using hzero
  have hmove := MarkerNavigation.boundaryTape_move_left registers
    (registerGap register)
  have hfinish := MarkerNavigation.lastGapTape_moveN_left registers
    (registerGap register)
  rw [registerGap_succ] at hmove
  rw [hvalue, FullTM0.Tape.moveN_zero] at hfinish
  exact hmove.trans hfinish

/-- Consequently the complete zero branch returns to the boundary-`4` anchor
without changing the register layout. -/
theorem zeroRecovery_executes (registers : Registers) (register : Register)
    (hzero : registers.get register = 0) :
    MarkerValidation.Executes (routeFromZero register)
      ((boundaryTape registers
        (decrementStartBoundary register)).move .left)
      (boundaryTape registers 4) := by
  rw [zeroTest_move_left registers register hzero]
  exact routeFromZero_executes registers register

/-- On a positive selected register, the test's left step scans a blank. -/
theorem positiveTest_read_blank (registers : Registers)
    (register : Register) (hpositive : 0 < registers.get register) :
    ((boundaryTape registers
      (decrementStartBoundary register)).move .left).read =
        MarkerMachine.blankSymbol := by
  have hvalue : 0 < RegisterLayout.values registers
      (registerGap register) := by
    cases register <;>
      simpa [RegisterLayout.values, Registers.get] using hpositive
  rw [← registerGap_succ]
  rw [MarkerNavigation.boundaryTape_move_left]
  exact (MarkerNavigation.lastGapTape_search_left registers
    (registerGap register)).blank hvalue

/-- Moving right after the positive blank test restores the exact decrement
schedule entry tape. -/
theorem positiveTest_move_right (registers : Registers)
    (register : Register) :
    (((boundaryTape registers
      (decrementStartBoundary register)).move .left).move .right) =
        boundaryTape registers (decrementStartBoundary register) := by
  simp

/-- A positive decrement schedule's final left step returns directly to the
boundary-`4` anchor of the decremented layout. -/
theorem decrementFinish_returnsToAnchor (registers : Registers)
    (register : Register) :
    (decrementFinishTape registers register).move .left =
      boundaryTape (registers.decrement register) 4 :=
  MarkerNavigation.decrementFinishTape_move_left registers register

end AnchoredCounterGeometry
end Hooper
end Kari
end LeanWang
