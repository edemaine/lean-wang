/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Bi-infinite Beatty representations

Section 5.1 of Jeandel and Vanier's presentation of Kari's construction uses
the first differences of the Beatty sequence to represent a real number on a
bi-infinite row.  This file records the construction and its two exact facts:
finite sums telescope, and every interval average differs from the represented
real by less than `1 / n`.

Keeping the starting position in `Int` is important: transducer rows are
bi-infinite even though each limiting average uses a finite interval.
-/

namespace LeanWang
namespace Kari

open scoped BigOperators

noncomputable section

namespace Beatty

/-- The integer Beatty sequence `i ↦ ⌊i α⌋`, indexed on the whole integer
line. -/
def sequence (alpha : ℝ) (i : Int) : Int :=
  ⌊(i : ℝ) * alpha⌋

/-- First differences of the Beatty sequence. -/
def digit (alpha : ℝ) (i : Int) : Int :=
  sequence alpha (i + 1) - sequence alpha i

/-- Beatty digits telescope on every finite interval of the integer line. -/
theorem sum_digit (alpha : ℝ) (start : Int) (n : Nat) :
    ∑ k ∈ Finset.range n, digit alpha (start + (k : Int)) =
      sequence alpha (start + (n : Int)) - sequence alpha start := by
  induction n with
  | zero => simp [sequence]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [digit]
      have hindex : start + (n : Int) + 1 = start + ((n + 1 : Nat) : Int) := by
        omega
      rw [hindex]
      ring

/-- The error of replacing a real by its floor lies in the half-open unit
interval. -/
theorem floor_error_bounds (x : ℝ) :
    0 ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) < 1 := by
  constructor
  · exact sub_nonneg.mpr (Int.floor_le x)
  · have h := Int.lt_floor_add_one x
    linarith

/-- The sum of the Beatty digits on any interval differs from `n * alpha` by
strictly less than one. -/
theorem abs_sum_digit_sub (alpha : ℝ) (start : Int) (n : Nat) :
    |((∑ k ∈ Finset.range n, digit alpha (start + (k : Int))) : Int) -
        (n : ℝ) * alpha| < 1 := by
  rw [sum_digit]
  let x : ℝ := (start : ℝ) * alpha
  let y : ℝ := ((start + (n : Int) : Int) : ℝ) * alpha
  have hx := floor_error_bounds x
  have hy := floor_error_bounds y
  have hdelta : y - x = (n : ℝ) * alpha := by
    dsimp [x, y]
    push_cast
    ring
  have hrewrite :
      ((sequence alpha (start + (n : Int)) : ℝ) -
          (sequence alpha start : ℝ) -
          (n : ℝ) * alpha) =
        (x - (⌊x⌋ : ℝ)) - (y - (⌊y⌋ : ℝ)) := by
    change (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) - (n : ℝ) * alpha =
      (x - (⌊x⌋ : ℝ)) - (y - (⌊y⌋ : ℝ))
    linarith
  simp only [Int.cast_sub]
  rw [hrewrite]
  rw [abs_lt]
  constructor <;> linarith

/-- A bi-infinite integer row is a balanced representation of `alpha` when
every finite interval has Beatty's unit discrepancy bound. -/
def IsBalanced (row : Int → Int) (alpha : ℝ) : Prop :=
  ∀ (start : Int) (n : Nat),
    |(((∑ k ∈ Finset.range n, row (start + (k : Int))) : Int) : ℝ) -
        (n : ℝ) * alpha| < 1

/-- First differences of the Beatty sequence are balanced. -/
theorem digit_isBalanced (alpha : ℝ) : IsBalanced (digit alpha) alpha := by
  intro start n
  exact abs_sum_digit_sub alpha start n

end Beatty

end

end Kari
end LeanWang
