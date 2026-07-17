/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Kari.Beatty
import LeanWang.Kari.AffineTransducer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Beatty rows for integer-coded affine branches

This file supplies the constructive direction of Kari's affine transducer
lemma.  Real triples are represented by the componentwise first differences
of their floor sequences.  If `y` is the image of `x` under an integer-coded
affine branch, the canonical carry

`A ⌊i x⌋ + i u - d ⌊i y⌋`

is uniformly bounded and obeys the local integer carry equation between every
pair of consecutive Beatty digits.
-/

namespace LeanWang
namespace Kari

noncomputable section

namespace AffineBeatty

/-- Interpret an integer triple as a real triple. -/
def toReal (v : IntVector3) : Fin 3 → ℝ
  | ⟨0, _⟩ => v.x
  | ⟨1, _⟩ => v.y
  | ⟨2, _⟩ => v.z

/-- Apply an integer matrix to a real triple. -/
def mulReal (A : IntMatrix3) (v : Fin 3 → ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => A.xx * v 0 + A.xy * v 1 + A.xz * v 2
  | ⟨1, _⟩ => A.yx * v 0 + A.yy * v 1 + A.yz * v 2
  | ⟨2, _⟩ => A.zx * v 0 + A.zy * v 1 + A.zz * v 2

/-- Take the floor of a real triple componentwise. -/
def floorVector (v : Fin 3 → ℝ) : IntVector3 :=
  ⟨⌊v 0⌋, ⌊v 1⌋, ⌊v 2⌋⟩

/-- The componentwise floor of `i` times a real triple. -/
def floorAt (v : Fin 3 → ℝ) (i : Int) : IntVector3 :=
  floorVector fun j => (i : ℝ) * v j

/-- The three componentwise Beatty digits beginning at position `i`. -/
def digitVector (v : Fin 3 → ℝ) (i : Int) : IntVector3 :=
  ⟨Beatty.digit (v 0) i, Beatty.digit (v 1) i,
    Beatty.digit (v 2) i⟩

/-- A vector Beatty digit is the difference of consecutive componentwise
floor vectors. -/
theorem digitVector_eq (v : Fin 3 → ℝ) (i : Int) :
    digitVector v i =
      ⟨(floorAt v (i + 1)).x - (floorAt v i).x,
        (floorAt v (i + 1)).y - (floorAt v i).y,
        (floorAt v (i + 1)).z - (floorAt v i).z⟩ := by
  rfl

/-- The real affine equation represented by an integer-coded branch. -/
def Realizes (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) : Prop :=
  ∀ j,
    (branch.denominator : ℝ) * output j =
      mulReal branch.linearNumerator input j + toReal branch.offsetNumerator j

/-- The canonical numerator of the carry at position `i`. -/
def canonicalCarry (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int) : IntVector3 :=
  (branch.linearNumerator.mulVec (floorAt input i)).add
    ((IntVector3.smul i branch.offsetNumerator).add
      (IntVector3.smul (-(branch.denominator : Int)) (floorAt output i)))

/-- Consecutive canonical carries and Beatty digits satisfy the exact scaled
integer equation used by the finite affine transducer.  Boundedness is the
only part of this construction that needs the real affine hypothesis. -/
theorem canonicalCarry_localEquation (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int) :
    branch.LocalEquation (digitVector input i) (digitVector output i)
      (canonicalCarry branch input output i)
      (canonicalCarry branch input output (i + 1)) := by
  rcases branch.linearNumerator with ⟨xx, xy, xz, yx, yy, yz, zx, zy, zz⟩
  rcases branch.offsetNumerator with ⟨ux, uy, uz⟩
  simp only [IntegerAffineBranch.LocalEquation, canonicalCarry, digitVector,
    floorAt, floorVector, Beatty.digit, Beatty.sequence, IntMatrix3.mulVec,
    IntVector3.add, IntVector3.smul, IntVector3.mk.injEq]
  constructor
  · ring
  constructor <;> ring

/-- Fractional error in the `i`th floor sequence. -/
def floorError (alpha : ℝ) (i : Int) : ℝ :=
  (i : ℝ) * alpha - (Beatty.sequence alpha i : ℝ)

theorem floorError_bounds (alpha : ℝ) (i : Int) :
    0 ≤ floorError alpha i ∧ floorError alpha i < 1 := by
  simpa [floorError, Beatty.sequence] using
    Beatty.floor_error_bounds ((i : ℝ) * alpha)

/-- Multiplying a floor error by an integer coefficient is bounded by the
absolute value of that coefficient. -/
theorem abs_int_mul_floorError_le (a : Int) (alpha : ℝ) (i : Int) :
    |(a : ℝ) * floorError alpha i| ≤ (a.natAbs : ℝ) := by
  have herr := floorError_bounds alpha i
  have habsError : |floorError alpha i| ≤ 1 := by
    rw [abs_of_nonneg herr.1]
    exact herr.2.le
  calc
    |(a : ℝ) * floorError alpha i| =
        |(a : ℝ)| * |floorError alpha i| := abs_mul _ _
    _ ≤ |(a : ℝ)| * 1 :=
      mul_le_mul_of_nonneg_left habsError (abs_nonneg _)
    _ = (a.natAbs : ℝ) := by
      simp only [mul_one, Nat.cast_natAbs, Int.cast_abs]

private theorem abs_sub_three_le
    (w x y z W X Y Z : ℝ)
    (hw : |w| ≤ W) (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |w - (x + y + z)| ≤ W + X + Y + Z := by
  rcases (abs_le.mp hw) with ⟨hwLower, hwUpper⟩
  rcases (abs_le.mp hx) with ⟨hxLower, hxUpper⟩
  rcases (abs_le.mp hy) with ⟨hyLower, hyUpper⟩
  rcases (abs_le.mp hz) with ⟨hzLower, hzUpper⟩
  rw [abs_le]
  constructor <;> linarith

/-- A deliberately crude common carry bound: the denominator plus the sum of
the absolute values of all nine matrix entries.  Using all rows keeps one
simple bound for all three carry coordinates. -/
def carryBound (branch : IntegerAffineBranch) : Nat :=
  branch.denominator +
    branch.linearNumerator.xx.natAbs +
    branch.linearNumerator.xy.natAbs +
    branch.linearNumerator.xz.natAbs +
    branch.linearNumerator.yx.natAbs +
    branch.linearNumerator.yy.natAbs +
    branch.linearNumerator.yz.natAbs +
    branch.linearNumerator.zx.natAbs +
    branch.linearNumerator.zy.natAbs +
    branch.linearNumerator.zz.natAbs

private theorem canonicalCarry_x_cast (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    ((canonicalCarry branch input output i).x : ℝ) =
      (branch.denominator : ℝ) * floorError (output 0) i -
        ((branch.linearNumerator.xx : ℝ) * floorError (input 0) i +
          (branch.linearNumerator.xy : ℝ) * floorError (input 1) i +
          (branch.linearNumerator.xz : ℝ) * floorError (input 2) i) := by
  have hcoordinate := hrealizes (0 : Fin 3)
  simp only [mulReal, toReal] at hcoordinate
  have hscaled := congrArg (fun r : ℝ => (i : ℝ) * r) hcoordinate
  simp only [canonicalCarry, floorAt, floorVector, IntMatrix3.mulVec,
    IntVector3.add, IntVector3.smul, floorError, Beatty.sequence]
  push_cast
  nlinarith [hscaled]

private theorem canonicalCarry_y_cast (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    ((canonicalCarry branch input output i).y : ℝ) =
      (branch.denominator : ℝ) * floorError (output 1) i -
        ((branch.linearNumerator.yx : ℝ) * floorError (input 0) i +
          (branch.linearNumerator.yy : ℝ) * floorError (input 1) i +
          (branch.linearNumerator.yz : ℝ) * floorError (input 2) i) := by
  have hcoordinate := hrealizes (1 : Fin 3)
  simp only [mulReal, toReal] at hcoordinate
  have hscaled := congrArg (fun r : ℝ => (i : ℝ) * r) hcoordinate
  simp only [canonicalCarry, floorAt, floorVector, IntMatrix3.mulVec,
    IntVector3.add, IntVector3.smul, floorError, Beatty.sequence]
  push_cast
  nlinarith [hscaled]

private theorem canonicalCarry_z_cast (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    ((canonicalCarry branch input output i).z : ℝ) =
      (branch.denominator : ℝ) * floorError (output 2) i -
        ((branch.linearNumerator.zx : ℝ) * floorError (input 0) i +
          (branch.linearNumerator.zy : ℝ) * floorError (input 1) i +
          (branch.linearNumerator.zz : ℝ) * floorError (input 2) i) := by
  have hcoordinate := hrealizes (2 : Fin 3)
  simp only [mulReal, toReal] at hcoordinate
  have hscaled := congrArg (fun r : ℝ => (i : ℝ) * r) hcoordinate
  simp only [canonicalCarry, floorAt, floorVector, IntMatrix3.mulVec,
    IntVector3.add, IntVector3.smul, floorError, Beatty.sequence]
  push_cast
  nlinarith [hscaled]

private theorem denominator_floorError_le (d : Nat) (alpha : ℝ) (i : Int) :
    |(d : ℝ) * floorError alpha i| ≤ (d : ℝ) := by
  simpa using abs_int_mul_floorError_le (d : Int) alpha i

private theorem canonicalCarry_x_abs_le (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    |((canonicalCarry branch input output i).x : ℝ)| ≤
      ((branch.denominator +
        branch.linearNumerator.xx.natAbs +
        branch.linearNumerator.xy.natAbs +
        branch.linearNumerator.xz.natAbs : Nat) : ℝ) := by
  rw [canonicalCarry_x_cast branch input output i hrealizes]
  simpa only [Nat.cast_add] using
    abs_sub_three_le
      ((branch.denominator : ℝ) * floorError (output 0) i)
      ((branch.linearNumerator.xx : ℝ) * floorError (input 0) i)
      ((branch.linearNumerator.xy : ℝ) * floorError (input 1) i)
      ((branch.linearNumerator.xz : ℝ) * floorError (input 2) i)
      (branch.denominator : ℝ)
      (branch.linearNumerator.xx.natAbs : ℝ)
      (branch.linearNumerator.xy.natAbs : ℝ)
      (branch.linearNumerator.xz.natAbs : ℝ)
      (denominator_floorError_le branch.denominator (output 0) i)
      (abs_int_mul_floorError_le branch.linearNumerator.xx (input 0) i)
      (abs_int_mul_floorError_le branch.linearNumerator.xy (input 1) i)
      (abs_int_mul_floorError_le branch.linearNumerator.xz (input 2) i)

private theorem canonicalCarry_y_abs_le (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    |((canonicalCarry branch input output i).y : ℝ)| ≤
      ((branch.denominator +
        branch.linearNumerator.yx.natAbs +
        branch.linearNumerator.yy.natAbs +
        branch.linearNumerator.yz.natAbs : Nat) : ℝ) := by
  rw [canonicalCarry_y_cast branch input output i hrealizes]
  simpa only [Nat.cast_add] using
    abs_sub_three_le
      ((branch.denominator : ℝ) * floorError (output 1) i)
      ((branch.linearNumerator.yx : ℝ) * floorError (input 0) i)
      ((branch.linearNumerator.yy : ℝ) * floorError (input 1) i)
      ((branch.linearNumerator.yz : ℝ) * floorError (input 2) i)
      (branch.denominator : ℝ)
      (branch.linearNumerator.yx.natAbs : ℝ)
      (branch.linearNumerator.yy.natAbs : ℝ)
      (branch.linearNumerator.yz.natAbs : ℝ)
      (denominator_floorError_le branch.denominator (output 1) i)
      (abs_int_mul_floorError_le branch.linearNumerator.yx (input 0) i)
      (abs_int_mul_floorError_le branch.linearNumerator.yy (input 1) i)
      (abs_int_mul_floorError_le branch.linearNumerator.yz (input 2) i)

private theorem canonicalCarry_z_abs_le (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (i : Int)
    (hrealizes : Realizes branch input output) :
    |((canonicalCarry branch input output i).z : ℝ)| ≤
      ((branch.denominator +
        branch.linearNumerator.zx.natAbs +
        branch.linearNumerator.zy.natAbs +
        branch.linearNumerator.zz.natAbs : Nat) : ℝ) := by
  rw [canonicalCarry_z_cast branch input output i hrealizes]
  simpa only [Nat.cast_add] using
    abs_sub_three_le
      ((branch.denominator : ℝ) * floorError (output 2) i)
      ((branch.linearNumerator.zx : ℝ) * floorError (input 0) i)
      ((branch.linearNumerator.zy : ℝ) * floorError (input 1) i)
      ((branch.linearNumerator.zz : ℝ) * floorError (input 2) i)
      (branch.denominator : ℝ)
      (branch.linearNumerator.zx.natAbs : ℝ)
      (branch.linearNumerator.zy.natAbs : ℝ)
      (branch.linearNumerator.zz.natAbs : ℝ)
      (denominator_floorError_le branch.denominator (output 2) i)
      (abs_int_mul_floorError_le branch.linearNumerator.zx (input 0) i)
      (abs_int_mul_floorError_le branch.linearNumerator.zy (input 1) i)
      (abs_int_mul_floorError_le branch.linearNumerator.zz (input 2) i)

private theorem int_bounds_of_abs_cast_le (z : Int) (bound : Nat)
    (h : |(z : ℝ)| ≤ (bound : ℝ)) :
    -(bound : Int) ≤ z ∧ z ≤ (bound : Int) := by
  rcases (abs_le.mp h) with ⟨hlower, hupper⟩
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

/-- Every canonical carry belongs to one fixed finite carry box, independently
of its position on the bi-infinite row. -/
theorem canonicalCarry_mem_bounded (branch : IntegerAffineBranch)
    (input output : Fin 3 → ℝ) (hrealizes : Realizes branch input output)
    (i : Int) :
    canonicalCarry branch input output i ∈
      IntVector3.bounded (carryBound branch) := by
  rw [IntVector3.mem_bounded]
  have hxRow := canonicalCarry_x_abs_le branch input output i hrealizes
  have hyRow := canonicalCarry_y_abs_le branch input output i hrealizes
  have hzRow := canonicalCarry_z_abs_le branch input output i hrealizes
  have hxNat :
      branch.denominator + branch.linearNumerator.xx.natAbs +
          branch.linearNumerator.xy.natAbs + branch.linearNumerator.xz.natAbs ≤
        carryBound branch := by
    simp only [carryBound]
    omega
  have hyNat :
      branch.denominator + branch.linearNumerator.yx.natAbs +
          branch.linearNumerator.yy.natAbs + branch.linearNumerator.yz.natAbs ≤
        carryBound branch := by
    simp only [carryBound]
    omega
  have hzNat :
      branch.denominator + branch.linearNumerator.zx.natAbs +
          branch.linearNumerator.zy.natAbs + branch.linearNumerator.zz.natAbs ≤
        carryBound branch := by
    simp only [carryBound]
    omega
  have hx : |((canonicalCarry branch input output i).x : ℝ)| ≤
      (carryBound branch : ℝ) :=
    hxRow.trans (by exact_mod_cast hxNat)
  have hy : |((canonicalCarry branch input output i).y : ℝ)| ≤
      (carryBound branch : ℝ) :=
    hyRow.trans (by exact_mod_cast hyNat)
  have hz : |((canonicalCarry branch input output i).z : ℝ)| ≤
      (carryBound branch : ℝ) :=
    hzRow.trans (by exact_mod_cast hzNat)
  rcases int_bounds_of_abs_cast_le _ _ hx with ⟨hxLower, hxUpper⟩
  rcases int_bounds_of_abs_cast_le _ _ hy with ⟨hyLower, hyUpper⟩
  rcases int_bounds_of_abs_cast_le _ _ hz with ⟨hzLower, hzUpper⟩
  exact ⟨hxLower, hxUpper, hyLower, hyUpper, hzLower, hzUpper⟩

/-- Once the two Beatty digits are included in the chosen finite alphabets,
their canonical transition is emitted by the finite transducer. -/
theorem canonical_transition_mem_transducer (branch : IntegerAffineBranch)
    (inputs outputs : List IntVector3) (input output : Fin 3 → ℝ)
    (hrealizes : Realizes branch input output) (i : Int)
    (hinput : digitVector input i ∈ inputs)
    (houtput : digitVector output i ∈ outputs) :
    branch.transition (digitVector input i) (digitVector output i)
        (canonicalCarry branch input output i)
        (canonicalCarry branch input output (i + 1)) ∈
      branch.transducer inputs outputs (carryBound branch) := by
  rw [IntegerAffineBranch.mem_transducer_iff]
  exact ⟨digitVector input i, digitVector output i,
    canonicalCarry branch input output i,
    canonicalCarry branch input output (i + 1),
    hinput, houtput,
    canonicalCarry_mem_bounded branch input output hrealizes i,
    canonicalCarry_mem_bounded branch input output hrealizes (i + 1),
    canonicalCarry_localEquation branch input output i, rfl⟩

end AffineBeatty

end

end Kari
end LeanWang
