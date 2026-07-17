/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Hooper.SearchGeometry

/-!
# Sparse counter layouts for Hooper's construction

Hooper represents a tuple of counters by marked tape cells separated by blank
gaps.  If `v i` is the value of counter `i`, consecutive boundary positions
satisfy

`boundaryPos v (i + 1) = boundaryPos v i + v i + 1`.

Thus incrementing one counter moves every later boundary exactly one cell to
the right and leaves every earlier boundary fixed.  This file isolates that
arithmetic independently of the transition table which will realize the move
by guarded searches.  Natural-number positions are used here; a concrete tape
embedding may translate the entire layout to any integer origin.
-/

namespace LeanWang
namespace Kari
namespace Hooper
namespace CounterLayout

open Turing

/-- Position of boundary `j` in the sparse marker representation of `v`.
Boundary zero is the origin, and counter `i` is the blank gap between
boundaries `i` and `i + 1`. -/
def boundaryPos (v : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => boundaryPos v i + v i + 1

@[simp]
theorem boundaryPos_zero (v : Nat → Nat) :
    boundaryPos v 0 = 0 :=
  rfl

@[simp]
theorem boundaryPos_succ (v : Nat → Nat) (i : Nat) :
    boundaryPos v (i + 1) = boundaryPos v i + v i + 1 :=
  rfl

/-- Boundary positions are strictly increasing, even when a counter is zero. -/
theorem boundaryPos_strictMono (v : Nat → Nat) :
    StrictMono (boundaryPos v) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [boundaryPos_succ]
  omega

/-- Boundary positions are monotone. -/
theorem boundaryPos_mono (v : Nat → Nat) :
    Monotone (boundaryPos v) :=
  (boundaryPos_strictMono v).monotone

/-- The value of counter `i` is exactly the number of cells strictly between
its two boundary markers. -/
theorem boundaryPos_gap (v : Nat → Nat) (i : Nat) :
    boundaryPos v (i + 1) - boundaryPos v i - 1 = v i := by
  simp only [boundaryPos_succ]
  omega

/-- A cell reached after at most `v i` steps from the first cell of gap `i`
does not pass its right boundary. -/
theorem firstGapCell_add_le_boundary (v : Nat → Nat) (i k : Nat)
    (hk : k ≤ v i) :
    boundaryPos v i + 1 + k ≤ boundaryPos v (i + 1) := by
  simp only [boundaryPos_succ]
  omega

/-- The first `v i` cells after boundary `i` are strictly before boundary
`i + 1`. -/
theorem firstGapCell_add_lt_boundary (v : Nat → Nat) (i k : Nat)
    (hk : k < v i) :
    boundaryPos v i + 1 + k < boundaryPos v (i + 1) := by
  simp only [boundaryPos_succ]
  omega

/-- After traversing all `v i` blank cells, the next position is precisely the
right boundary. -/
theorem firstGapCell_add_value (v : Nat → Nat) (i : Nat) :
    boundaryPos v i + 1 + v i = boundaryPos v (i + 1) := by
  simp only [boundaryPos_succ]
  omega

/-- No boundary marker lies strictly inside a counter gap. -/
theorem boundaryPos_ne_firstGapCell_add (v : Nat → Nat) (i j k : Nat)
    (hk : k < v i) :
    boundaryPos v j ≠ boundaryPos v i + 1 + k := by
  intro h
  by_cases hj : j ≤ i
  · have hle : boundaryPos v j ≤ boundaryPos v i :=
      boundaryPos_mono v hj
    omega
  · have hij : i + 1 ≤ j := by omega
    have hle : boundaryPos v (i + 1) ≤ boundaryPos v j :=
      boundaryPos_mono v hij
    have hlt := firstGapCell_add_lt_boundary v i k hk
    omega

/-- Add `amount` to counter `r`. -/
def add (v : Nat → Nat) (r amount : Nat) : Nat → Nat :=
  Function.update v r (v r + amount)

/-- Adding to one counter translates exactly the suffix of later boundary
positions.  This is the arithmetic invariant behind a right-to-left suffix
shift in the marker machine. -/
theorem boundaryPos_add (v : Nat → Nat) (r amount j : Nat) :
    boundaryPos (add v r amount) j =
      boundaryPos v j + if r < j then amount else 0 := by
  induction j with
  | zero => simp [boundaryPos]
  | succ j ih =>
      simp only [boundaryPos_succ, ih]
      by_cases hrj : r = j
      · subst r
        simp [add]
        omega
      · have hjr : j ≠ r := Ne.symm hrj
        rw [show add v r amount j = v j by simp [add, hjr]]
        by_cases hrlt : r < j
        · simp [hrlt, Nat.lt_succ_of_lt hrlt]
          omega
        · have hrsucc : ¬ r < j + 1 := by omega
          simp [hrlt, hrsucc]

/-- Increment one counter. -/
def increment (v : Nat → Nat) (r : Nat) : Nat → Nat :=
  add v r 1

/-- Incrementing counter `r` leaves boundary `j` fixed when `j ≤ r`. -/
theorem boundaryPos_increment_of_le (v : Nat → Nat) (r j : Nat)
    (hj : j ≤ r) :
    boundaryPos (increment v r) j = boundaryPos v j := by
  rw [increment, boundaryPos_add]
  simp [Nat.not_lt_of_ge hj]

/-- Incrementing counter `r` moves boundary `j` one cell right when `r < j`. -/
theorem boundaryPos_increment_of_lt (v : Nat → Nat) (r j : Nat)
    (hj : r < j) :
    boundaryPos (increment v r) j = boundaryPos v j + 1 := by
  rw [increment, boundaryPos_add]
  simp [hj]

/-- Decrement counter `r`, saturating at zero.  Concrete machine code invokes
this operation only after a successful nonzero test. -/
def decrement (v : Nat → Nat) (r : Nat) : Nat → Nat :=
  Function.update v r (v r - 1)

/-- A positive decrement is inverse to incrementing the resulting layout. -/
theorem increment_decrement (v : Nat → Nat) (r : Nat) (hr : 0 < v r) :
    increment (decrement v r) r = v := by
  funext i
  by_cases hi : i = r
  · subst i
    simp [increment, add, decrement]
    omega
  · simp [increment, add, decrement, hi]

/-- Decrementing a positive counter translates exactly the suffix of later
boundaries one cell to the left.  The equality is oriented without truncated
subtraction, which is the form used by marker-shift correctness proofs. -/
theorem boundaryPos_decrement (v : Nat → Nat) (r j : Nat) (hr : 0 < v r) :
    boundaryPos v j = boundaryPos (decrement v r) j +
      if r < j then 1 else 0 := by
  calc
    boundaryPos v j = boundaryPos (increment (decrement v r) r) j := by
      rw [increment_decrement v r hr]
    _ = boundaryPos (decrement v r) j + if r < j then 1 else 0 := by
      exact boundaryPos_add (decrement v r) r 1 j

/-- A positive decrement leaves boundary `j` fixed when `j ≤ r`. -/
theorem boundaryPos_decrement_of_le (v : Nat → Nat) (r j : Nat)
    (hr : 0 < v r) (hj : j ≤ r) :
    boundaryPos (decrement v r) j = boundaryPos v j := by
  have h := boundaryPos_decrement v r j hr
  simp [Nat.not_lt_of_ge hj] at h
  exact h.symm

/-- A positive decrement moves every later boundary one cell left. -/
theorem boundaryPos_decrement_of_lt (v : Nat → Nat) (r j : Nat)
    (hr : 0 < v r) (hj : r < j) :
    boundaryPos (decrement v r) j + 1 = boundaryPos v j := by
  simpa [hj] using (boundaryPos_decrement v r j hr).symm

/-- Integer-valued tape whose head starts at the first cell after boundary
`i`.  Its values are absolute tape coordinates, which lets the following
predicate describe marker positions without choosing marker labels. -/
def firstGapCellTape (v : Nat → Nat) (i : Nat) : FullTM0.Tape Int :=
  fun offset => (boundaryPos v i : Int) + 1 + offset

/-- An absolute coordinate is occupied by one of the sparse layout's boundary
markers. -/
def IsBoundary (v : Nat → Nat) (position : Int) : Prop :=
  ∃ j, position = boundaryPos v j

/-- An absolute coordinate is blank precisely when it is not a boundary. -/
def IsBlank (v : Nat → Nat) (position : Int) : Prop :=
  ¬ IsBoundary v position

/-- Looking right from the first cell after boundary `i` sees exactly `v i`
blank cells followed by boundary `i + 1`.  This is the bridge from sparse
counter arithmetic to the search geometry used by Hooper's Basic Lemma. -/
theorem searchGap_firstGapCellTape (v : Nat → Nat) (i : Nat) :
    SearchGap (IsBlank v) (IsBoundary v) (firstGapCellTape v i)
      .right (v i) := by
  constructor
  · intro k hk
    rw [IsBlank, IsBoundary]
    rintro ⟨j, hj⟩
    have hnat : boundaryPos v j = boundaryPos v i + 1 + k := by
      simp only [firstGapCellTape, FullTM0.Tape.offset_right] at hj
      exact_mod_cast hj.symm
    exact boundaryPos_ne_firstGapCell_add v i j k hk hnat
  · refine ⟨i + 1, ?_⟩
    simp only [firstGapCellTape, FullTM0.Tape.offset_right]
    exact_mod_cast firstGapCell_add_value v i

/-- Integer-valued tape whose head starts at the last cell before boundary
`i + 1`. -/
def lastGapCellTape (v : Nat → Nat) (i : Nat) : FullTM0.Tape Int :=
  fun offset => (boundaryPos v (i + 1) : Int) - 1 + offset

/-- The same counter gap can be searched from right to left: the first `v i`
positions are blank and the next position is boundary `i`. -/
theorem searchGap_lastGapCellTape (v : Nat → Nat) (i : Nat) :
    SearchGap (IsBlank v) (IsBoundary v) (lastGapCellTape v i)
      .left (v i) := by
  have hsucc : (boundaryPos v (i + 1) : Int) =
      boundaryPos v i + v i + 1 := by
    exact_mod_cast boundaryPos_succ v i
  constructor
  · intro k hk
    rw [IsBlank, IsBoundary]
    rintro ⟨j, hj⟩
    let t := v i - 1 - k
    have ht : t < v i := by
      dsimp [t]
      omega
    have hjInt : (boundaryPos v j : Int) =
        (boundaryPos v i : Int) + 1 + t := by
      simp only [lastGapCellTape, FullTM0.Tape.offset_left] at hj
      dsimp [t]
      rw [hsucc] at hj
      omega
    have hjNat : boundaryPos v j = boundaryPos v i + 1 + t := by
      exact_mod_cast hjInt
    exact boundaryPos_ne_firstGapCell_add v i j t ht hjNat
  · refine ⟨i, ?_⟩
    simp only [lastGapCellTape, FullTM0.Tape.offset_left]
    rw [hsucc]
    norm_num

end CounterLayout
end Hooper
end Kari
end LeanWang
