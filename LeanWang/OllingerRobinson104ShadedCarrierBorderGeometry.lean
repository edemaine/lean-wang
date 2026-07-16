/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierBorderHierarchy
import Mathlib.Data.Nat.Periodic

/-!
# Arithmetic geometry of the selected-border hierarchy

This module characterizes the canonical nearest-border paths of the corrected
union-of-frames border formula.  The first step is the exact scaling relation
between consecutive frame depths.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderGeometry

open ShadedCarrierHierarchy ShadedCarrierBorderHierarchy

theorem ceilDivFour_add_four_mul (coordinate multiple : Nat) :
    ceilDivFour (coordinate + 4 * multiple) =
      ceilDivFour coordinate + multiple := by
  unfold ceilDivFour
  rw [show coordinate + 4 * multiple + 3 =
      (coordinate + 3) + 4 * multiple by omega]
  exact Nat.add_mul_div_left (coordinate + 3) multiple (y := 4) (by decide)

theorem ceilDivFour_four_mul_sub_three (n : Nat) (positive : 0 < n) :
    ceilDivFour (4 * n - 3) = n := by
  unfold ceilDivFour
  have threeLe : 3 ≤ 4 * n := by omega
  rw [Nat.sub_add_cancel threeLe]
  omega

theorem period_succ (depth : Nat) :
    period (depth + 1) = 4 * period depth := by
  simp [period, pow_succ, Nat.mul_comm]

theorem frameStartResidue_succ (depth : Nat) :
    frameStartResidue (depth + 1) = 4 * frameStartResidue depth - 3 := by
  simp only [frameStartResidue, scale, pow_succ]
  have positive : 0 < 4 ^ depth := pow_pos (by decide) _
  omega

theorem frameEndResidue_succ (depth : Nat) :
    frameEndResidue (depth + 1) = 4 * frameEndResidue depth := by
  simp [frameEndResidue, scale, pow_succ, Nat.mul_comm, Nat.mul_left_comm]

private theorem inFrame_ceilDivFour_periodic (depth : Nat) :
    Function.Periodic (fun coordinate =>
      inFrame depth (ceilDivFour coordinate)) (period (depth + 1)) := by
  intro coordinate
  rw [period_succ]
  change inFrame depth (ceilDivFour (coordinate + 4 * period depth)) = _
  rw [ceilDivFour_add_four_mul]
  simp [inFrame]

private theorem inFrame_periodic (depth : Nat) :
    Function.Periodic (inFrame depth) (period depth) := by
  intro coordinate
  simp [inFrame]

theorem inFrame_succ_iff_ceilDivFour (depth coordinate : Nat) :
    inFrame (depth + 1) coordinate =
      inFrame depth (ceilDivFour coordinate) := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (pow_pos (by decide) _)
  rw [← (inFrame_periodic (depth + 1)).map_mod_nat coordinate]
  rw [← (inFrame_ceilDivFour_periodic depth).map_mod_nat coordinate]
  change inFrame (depth + 1) residue =
    inFrame depth (ceilDivFour residue)
  have periodEq := period_succ depth
  have startEq := frameStartResidue_succ depth
  have endEq := frameEndResidue_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour
    rw [periodEq] at residueLt
    omega
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [inFrame, inFrame, Nat.mod_eq_of_lt residueLt,
      Nat.mod_eq_of_lt coarseLt]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold ceilDivFour
    omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    have scalePositive : 0 < scale depth := pow_pos (by decide) _
    have fineFalse : inFrame (depth + 1) residue = false := by
      apply Bool.eq_false_iff.mpr
      intro inside
      have insideData :
          frameStartResidue (depth + 1) ≤ residue ∧
            residue ≤ frameEndResidue (depth + 1) := by
        simpa only [inFrame, Nat.mod_eq_of_lt residueLt,
          Bool.and_eq_true, decide_eq_true_eq] using inside
      unfold ceilDivFour at coarseEq
      rw [endEq] at insideData
      have periodScale := period_eq_four_mul_scale depth
      simp only [frameEndResidue] at insideData
      omega
    have coarseFalse :
        inFrame depth (ceilDivFour residue) = false := by
      rw [coarseEq]
      simp [inFrame, frameStartResidue]
    rw [fineFalse, coarseFalse]

private theorem openingLiftCondition_periodic (depth : Nat) :
    Function.Periodic (fun coordinate =>
      ceilDivFour coordinate % period depth = frameStartResidue depth ∧
        coordinate % 4 = 1) (period (depth + 1)) := by
  intro coordinate
  rw [period_succ]
  apply propext
  change
    ceilDivFour (coordinate + 4 * period depth) % period depth = _ ∧
        (coordinate + 4 * period depth) % 4 = 1 ↔ _
  rw [ceilDivFour_add_four_mul]
  simp

private theorem openingBoundary_periodic (depth : Nat) :
    Function.Periodic (fun coordinate =>
      coordinate % period (depth + 1) = frameStartResidue (depth + 1))
      (period (depth + 1)) := by
  intro coordinate
  simp

theorem openingBoundary_succ_iff (depth coordinate : Nat) :
    coordinate % period (depth + 1) = frameStartResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameStartResidue depth ∧
        coordinate % 4 = 1 := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (pow_pos (by decide) _)
  rw [← (openingBoundary_periodic depth).map_mod_nat coordinate]
  rw [← (openingLiftCondition_periodic depth).map_mod_nat coordinate]
  change residue % period (depth + 1) = frameStartResidue (depth + 1) ↔
    ceilDivFour residue % period depth = frameStartResidue depth ∧
      residue % 4 = 1
  rw [Nat.mod_eq_of_lt residueLt]
  have periodEq := period_succ depth
  have startEq := frameStartResidue_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour
    rw [periodEq] at residueLt
    omega
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [Nat.mod_eq_of_lt coarseLt]
    rw [startEq]
    have startPositive : 0 < frameStartResidue depth := by
      simp [frameStartResidue]
    unfold ceilDivFour
    omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    rw [coarseEq, Nat.mod_self, startEq]
    have startPositive : 0 < frameStartResidue depth := by
      simp [frameStartResidue]
    have startLtPeriod : frameStartResidue depth < period depth := by
      rw [period_eq_four_mul_scale]
      simp only [frameStartResidue]
      have scalePositive : 0 < scale depth := pow_pos (by decide) _
      omega
    have leftFalse : residue ≠ 4 * frameStartResidue depth - 3 := by
      intro residueEq
      rw [residueEq,
        ceilDivFour_four_mul_sub_three _ startPositive] at coarseEq
      exact (Nat.ne_of_lt startLtPeriod) coarseEq
    constructor
    · intro left
      exact (leftFalse left).elim
    · rintro ⟨zeroEq, _⟩
      omega

private theorem closingLiftCondition_periodic (depth : Nat) :
    Function.Periodic (fun coordinate =>
      ceilDivFour coordinate % period depth = frameEndResidue depth ∧
        coordinate % 4 = 0) (period (depth + 1)) := by
  intro coordinate
  rw [period_succ]
  apply propext
  change
    ceilDivFour (coordinate + 4 * period depth) % period depth = _ ∧
        (coordinate + 4 * period depth) % 4 = 0 ↔ _
  rw [ceilDivFour_add_four_mul]
  simp

private theorem closingBoundary_periodic (depth : Nat) :
    Function.Periodic (fun coordinate =>
      coordinate % period (depth + 1) = frameEndResidue (depth + 1))
      (period (depth + 1)) := by
  intro coordinate
  simp

theorem closingBoundary_succ_iff (depth coordinate : Nat) :
    coordinate % period (depth + 1) = frameEndResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameEndResidue depth ∧
        coordinate % 4 = 0 := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (pow_pos (by decide) _)
  rw [← (closingBoundary_periodic depth).map_mod_nat coordinate]
  rw [← (closingLiftCondition_periodic depth).map_mod_nat coordinate]
  change residue % period (depth + 1) = frameEndResidue (depth + 1) ↔
    ceilDivFour residue % period depth = frameEndResidue depth ∧
      residue % 4 = 0
  rw [Nat.mod_eq_of_lt residueLt]
  have periodEq := period_succ depth
  have endEq := frameEndResidue_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour
    rw [periodEq] at residueLt
    omega
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [Nat.mod_eq_of_lt coarseLt]
    rw [endEq]
    have endPositive : 0 < frameEndResidue depth := by
      simp [frameEndResidue, scale, pow_pos]
    unfold ceilDivFour
    omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    rw [coarseEq, Nat.mod_self, endEq]
    have endPositive : 0 < frameEndResidue depth := by
      simp [frameEndResidue, scale, pow_pos]
    have scalePositive : 0 < scale depth := pow_pos (by decide) _
    have periodScale := period_eq_four_mul_scale depth
    unfold ceilDivFour at coarseEq
    rw [periodEq] at residueLt
    omega

theorem frameBorder_succ (depth coordinate transverse : Nat) :
    liftBorder coordinate
        (frameBorder depth (ceilDivFour coordinate)
          (ceilDivFour transverse)) =
      frameBorder (depth + 1) coordinate transverse := by
  rw [frameBorder, frameBorder,
    ← inFrame_succ_iff_ceilDivFour depth transverse]
  simp only [openingBoundary_succ_iff, closingBoundary_succ_iff]
  have boundaryDistinct :
      frameStartResidue depth ≠ frameEndResidue depth := by
    have scalePositive : 0 < scale depth := pow_pos (by decide) _
    simp only [frameStartResidue, frameEndResidue]
    omega
  have boundaryDistinctSymm :
      frameEndResidue depth ≠ frameStartResidue depth :=
    Ne.symm boundaryDistinct
  by_cases inside : inFrame (depth + 1) transverse <;>
    simp only [inside, if_true]
  · by_cases opening :
        ceilDivFour coordinate % period depth = frameStartResidue depth
    · by_cases fineOpening : coordinate % 4 = 1 <;>
        simp [liftBorder, opening, fineOpening, boundaryDistinct]
    · by_cases closing :
          ceilDivFour coordinate % period depth = frameEndResidue depth
      · by_cases fineClosing : coordinate % 4 = 0 <;>
          simp [liftBorder, closing, fineClosing, boundaryDistinctSymm]
      · simp [liftBorder, opening, closing]
  · rfl

end ShadedCarrierBorderGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
