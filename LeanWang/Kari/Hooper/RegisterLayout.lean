/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.CounterMachine
import LeanWang.Kari.Hooper.CounterLayout

/-!
# The four-register sparse layout

This file connects the named registers of `CounterMachine` to the generic
sparse marker arithmetic in `CounterLayout`.  The gaps occur in the fixed
order

`left, right, temp, clock`.

Consequently the layout has five named boundaries: the origin followed by
the right boundary of each of the four gaps.  Values at indices beyond the
four named registers are zero; this makes the representation a genuine
four-register layout even though `CounterLayout` accepts a function on all
natural-number indices.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace RegisterLayout

open Turing
open CounterMachine

/-- Index of a named register in the sparse marker layout. -/
def registerIndex : Register → Nat
  | .left => 0
  | .right => 1
  | .temp => 2
  | .clock => 3

@[simp] theorem registerIndex_left : registerIndex .left = 0 := rfl
@[simp] theorem registerIndex_right : registerIndex .right = 1 := rfl
@[simp] theorem registerIndex_temp : registerIndex .temp = 2 := rfl
@[simp] theorem registerIndex_clock : registerIndex .clock = 3 := rfl

/-- The named register tuple as the counter-value function expected by
`CounterLayout`.  Indices at least four are deliberately empty. -/
def values (v : Registers) : Nat → Nat
  | 0 => v.left
  | 1 => v.right
  | 2 => v.temp
  | 3 => v.clock
  | _ => 0

@[simp] theorem values_zero (v : Registers) : values v 0 = v.left := rfl
@[simp] theorem values_one (v : Registers) : values v 1 = v.right := rfl
@[simp] theorem values_two (v : Registers) : values v 2 = v.temp := rfl
@[simp] theorem values_three (v : Registers) : values v 3 = v.clock := rfl

@[simp]
theorem values_registerIndex (v : Registers) (r : Register) :
    values v (registerIndex r) = v.get r := by
  cases r <;> rfl

/-- There are no unnamed counters after the four named gaps. -/
@[simp]
theorem values_of_four_le (v : Registers) {i : Nat} (hi : 4 ≤ i) :
    values v i = 0 := by
  cases i with
  | zero => omega
  | succ i =>
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => omega
      | succ i =>
        cases i with
        | zero => omega
        | succ i => rfl

/-- The sparse value function loses no information from the register tuple. -/
theorem values_injective : Function.Injective values := by
  intro v w h
  have hleft := congrFun h 0
  have hright := congrFun h 1
  have htemp := congrFun h 2
  have hclock := congrFun h 3
  simp only [values_zero] at hleft
  simp only [values_one] at hright
  simp only [values_two] at htemp
  simp only [values_three] at hclock
  cases v
  cases w
  simp_all

/-- Updating a named register agrees exactly with updating its indexed gap. -/
theorem values_set (v : Registers) (r : Register) (n : Nat) :
    values (v.set r n) = Function.update (values v) (registerIndex r) n := by
  funext i
  cases i with
  | zero => cases r <;> simp [values, Registers.set, Function.update, registerIndex]
  | succ i =>
    cases i with
    | zero => cases r <;> simp [values, Registers.set, Function.update, registerIndex]
    | succ i =>
      cases i with
      | zero => cases r <;> simp [values, Registers.set, Function.update, registerIndex]
      | succ i =>
        cases i with
        | zero => cases r <;> simp [values, Registers.set, Function.update, registerIndex]
        | succ i => cases r <;> simp [values, Function.update, registerIndex]

/-- Named-register increment is generic sparse-layout increment. -/
theorem values_increment (v : Registers) (r : Register) :
    values (v.increment r) = CounterLayout.increment (values v) (registerIndex r) := by
  rw [Registers.increment, values_set]
  funext i
  simp [CounterLayout.increment, CounterLayout.add]

/-- Named-register decrement is generic saturating sparse-layout decrement. -/
theorem values_decrement (v : Registers) (r : Register) :
    values (v.decrement r) = CounterLayout.decrement (values v) (registerIndex r) := by
  rw [Registers.decrement, values_set]
  funext i
  simp [CounterLayout.decrement]

/-- The common left boundary of all four register gaps. -/
def startBoundary (v : Registers) : Nat :=
  CounterLayout.boundaryPos (values v) 0

/-- The right boundary of the `left` register gap. -/
def leftBoundary (v : Registers) : Nat :=
  CounterLayout.boundaryPos (values v) 1

/-- The right boundary of the `right` register gap. -/
def rightBoundary (v : Registers) : Nat :=
  CounterLayout.boundaryPos (values v) 2

/-- The right boundary of the `temp` register gap. -/
def tempBoundary (v : Registers) : Nat :=
  CounterLayout.boundaryPos (values v) 3

/-- The right boundary of the `clock` register gap, and the end of the
four-register layout. -/
def clockBoundary (v : Registers) : Nat :=
  CounterLayout.boundaryPos (values v) 4

@[simp] theorem startBoundary_eq (v : Registers) : startBoundary v = 0 := rfl

@[simp]
theorem leftBoundary_eq (v : Registers) :
    leftBoundary v = v.left + 1 := by
  simp [leftBoundary, CounterLayout.boundaryPos]

@[simp]
theorem rightBoundary_eq (v : Registers) :
    rightBoundary v = v.left + v.right + 2 := by
  simp [rightBoundary, CounterLayout.boundaryPos]
  omega

@[simp]
theorem tempBoundary_eq (v : Registers) :
    tempBoundary v = v.left + v.right + v.temp + 3 := by
  simp [tempBoundary, CounterLayout.boundaryPos]
  omega

@[simp]
theorem clockBoundary_eq (v : Registers) :
    clockBoundary v = v.left + v.right + v.temp + v.clock + 4 := by
  simp [clockBoundary, CounterLayout.boundaryPos]
  omega

/-- The first gap has exactly the value of the `left` register. -/
theorem left_gap (v : Registers) :
    leftBoundary v - startBoundary v - 1 = v.left := by
  simp

/-- The second gap has exactly the value of the `right` register. -/
theorem right_gap (v : Registers) :
    rightBoundary v - leftBoundary v - 1 = v.right := by
  simp
  omega

/-- The third gap has exactly the value of the `temp` register. -/
theorem temp_gap (v : Registers) :
    tempBoundary v - rightBoundary v - 1 = v.temp := by
  simp
  omega

/-- The fourth gap has exactly the value of the `clock` register. -/
theorem clock_gap (v : Registers) :
    clockBoundary v - tempBoundary v - 1 = v.clock := by
  simp
  omega

/-- Incrementing a named register moves precisely the suffix of boundaries
strictly after its gap. -/
theorem boundaryPos_increment (v : Registers) (r : Register) (j : Nat) :
    CounterLayout.boundaryPos (values (v.increment r)) j =
      CounterLayout.boundaryPos (values v) j +
        if registerIndex r < j then 1 else 0 := by
  rw [values_increment]
  simpa [CounterLayout.increment] using
    (CounterLayout.boundaryPos_add (values v) (registerIndex r) 1 j)

theorem boundaryPos_increment_left (v : Registers) (j : Nat) :
    CounterLayout.boundaryPos (values (v.increment .left)) j =
      CounterLayout.boundaryPos (values v) j + if 0 < j then 1 else 0 := by
  exact boundaryPos_increment v Register.left j

theorem boundaryPos_increment_right (v : Registers) (j : Nat) :
    CounterLayout.boundaryPos (values (v.increment .right)) j =
      CounterLayout.boundaryPos (values v) j + if 1 < j then 1 else 0 := by
  exact boundaryPos_increment v Register.right j

theorem boundaryPos_increment_temp (v : Registers) (j : Nat) :
    CounterLayout.boundaryPos (values (v.increment .temp)) j =
      CounterLayout.boundaryPos (values v) j + if 2 < j then 1 else 0 := by
  exact boundaryPos_increment v Register.temp j

theorem boundaryPos_increment_clock (v : Registers) (j : Nat) :
    CounterLayout.boundaryPos (values (v.increment .clock)) j =
      CounterLayout.boundaryPos (values v) j + if 3 < j then 1 else 0 := by
  exact boundaryPos_increment v Register.clock j

/-- A positive decrement moves precisely the suffix of boundaries strictly
after the named register one cell left.  The equality is oriented to avoid
truncated subtraction. -/
theorem boundaryPos_decrement (v : Registers) (r : Register) (j : Nat)
    (hr : 0 < v.get r) :
    CounterLayout.boundaryPos (values v) j =
      CounterLayout.boundaryPos (values (v.decrement r)) j +
        if registerIndex r < j then 1 else 0 := by
  rw [values_decrement]
  exact CounterLayout.boundaryPos_decrement (values v) (registerIndex r) j
    (by simpa using hr)

theorem boundaryPos_decrement_left (v : Registers) (j : Nat) (hr : 0 < v.left) :
    CounterLayout.boundaryPos (values v) j =
      CounterLayout.boundaryPos (values (v.decrement .left)) j +
        if 0 < j then 1 else 0 := by
  exact boundaryPos_decrement v Register.left j hr

theorem boundaryPos_decrement_right (v : Registers) (j : Nat) (hr : 0 < v.right) :
    CounterLayout.boundaryPos (values v) j =
      CounterLayout.boundaryPos (values (v.decrement .right)) j +
        if 1 < j then 1 else 0 := by
  exact boundaryPos_decrement v Register.right j hr

theorem boundaryPos_decrement_temp (v : Registers) (j : Nat) (hr : 0 < v.temp) :
    CounterLayout.boundaryPos (values v) j =
      CounterLayout.boundaryPos (values (v.decrement .temp)) j +
        if 2 < j then 1 else 0 := by
  exact boundaryPos_decrement v Register.temp j hr

theorem boundaryPos_decrement_clock (v : Registers) (j : Nat) (hr : 0 < v.clock) :
    CounterLayout.boundaryPos (values v) j =
      CounterLayout.boundaryPos (values (v.decrement .clock)) j +
        if 3 < j then 1 else 0 := by
  exact boundaryPos_decrement v Register.clock j hr

/-- A rightward search across the `left` register gap. -/
theorem searchGap_left_right (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.firstGapCellTape (values v) 0) .right v.left := by
  simpa using CounterLayout.searchGap_firstGapCellTape (values v) 0

/-- A leftward search across the `left` register gap. -/
theorem searchGap_left_left (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.lastGapCellTape (values v) 0) .left v.left := by
  simpa using CounterLayout.searchGap_lastGapCellTape (values v) 0

/-- A rightward search across the `right` register gap. -/
theorem searchGap_right_right (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.firstGapCellTape (values v) 1) .right v.right := by
  simpa using CounterLayout.searchGap_firstGapCellTape (values v) 1

/-- A leftward search across the `right` register gap. -/
theorem searchGap_right_left (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.lastGapCellTape (values v) 1) .left v.right := by
  simpa using CounterLayout.searchGap_lastGapCellTape (values v) 1

/-- A rightward search across the `temp` register gap. -/
theorem searchGap_temp_right (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.firstGapCellTape (values v) 2) .right v.temp := by
  simpa using CounterLayout.searchGap_firstGapCellTape (values v) 2

/-- A leftward search across the `temp` register gap. -/
theorem searchGap_temp_left (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.lastGapCellTape (values v) 2) .left v.temp := by
  simpa using CounterLayout.searchGap_lastGapCellTape (values v) 2

/-- A rightward search across the `clock` register gap. -/
theorem searchGap_clock_right (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.firstGapCellTape (values v) 3) .right v.clock := by
  simpa using CounterLayout.searchGap_firstGapCellTape (values v) 3

/-- A leftward search across the `clock` register gap. -/
theorem searchGap_clock_left (v : Registers) :
    SearchGap (CounterLayout.IsBlank (values v)) (CounterLayout.IsBoundary (values v))
      (CounterLayout.lastGapCellTape (values v) 3) .left v.clock := by
  simpa using CounterLayout.searchGap_lastGapCellTape (values v) 3

end RegisterLayout
end Hooper
end Kari
end LeanWang
