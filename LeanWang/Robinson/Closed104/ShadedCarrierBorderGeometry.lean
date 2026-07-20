/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderHierarchyData
import Mathlib.Data.Nat.Periodic

/-!
# Arithmetic geometry of the selected-border hierarchy

This module characterizes the canonical nearest-border paths of the corrected
union-of-frames border formula.  The first step is the exact scaling relation
between consecutive frame depths.

A depth-`d` frame repeats with period `4^(d+1)`.  Its opening and closing
coordinates are distinct residues in that period.  One substitution divides
coordinates by four, rounded upward; an opening survives only at fine residue
`1`, and a closing only at fine residue `0`.  This is precisely the behavior
implemented by `liftBorder`.

After proving that scaling law, the module shows that boundaries from different
depths cannot overlap.  Therefore the bounded search in `selectedBorder` is a
mathematical union of the outer opening and all frame boundaries, independent
of search priority.  Those facts are the arithmetic input to the finite-state
hierarchy proof.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderGeometry

open ShadedCarrierHierarchy ShadedCarrierBorderHierarchy

/- `ceilDivFour` is the coarse coordinate map for one substitution.  The next
lemmas establish how periods, frame interiors, and boundary residues transform
under it.  `FrameSide` packages the opening and closing calculations, whose
only asymmetry is fine residue 1 versus 0. -/

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

private inductive FrameSide where
  | opening
  | closing

private def FrameSide.boundaryResidue : FrameSide → Nat → Nat
  | .opening => frameStartResidue
  | .closing => frameEndResidue

private def FrameSide.fineResidue : FrameSide → Nat
  | .opening => 1
  | .closing => 0

private theorem FrameSide.boundaryResidue_pos
    (side : FrameSide) (depth : Nat) :
    0 < side.boundaryResidue depth := by
  cases side <;> simp [boundaryResidue, frameStartResidue,
    frameEndResidue, scale, pow_pos]

private theorem FrameSide.boundaryResidue_lt_period
    (side : FrameSide) (depth : Nat) :
    side.boundaryResidue depth < period depth := by
  have positive : 0 < scale depth := pow_pos (by decide) _
  rw [period_eq_four_mul_scale]
  cases side <;> simp only [boundaryResidue, frameStartResidue,
    frameEndResidue] <;> omega

private theorem FrameSide.ceilDivFour_boundaryResidue_succ
    (side : FrameSide) (depth : Nat) :
    ceilDivFour (side.boundaryResidue (depth + 1)) =
      side.boundaryResidue depth := by
  cases side <;>
    simp only [boundaryResidue, frameStartResidue, frameEndResidue,
      scale, pow_succ] <;>
    unfold ceilDivFour <;> omega

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

private theorem boundaryLiftCondition_periodic
    (side : FrameSide) (depth : Nat) :
    Function.Periodic (fun coordinate =>
      ceilDivFour coordinate % period depth = side.boundaryResidue depth ∧
        coordinate % 4 = side.fineResidue) (period (depth + 1)) := by
  intro coordinate
  rw [period_succ]
  apply propext
  change
    ceilDivFour (coordinate + 4 * period depth) % period depth = _ ∧
        (coordinate + 4 * period depth) % 4 = side.fineResidue ↔ _
  rw [ceilDivFour_add_four_mul]
  simp

private theorem boundary_periodic (side : FrameSide) (depth : Nat) :
    Function.Periodic (fun coordinate =>
      coordinate % period (depth + 1) = side.boundaryResidue (depth + 1))
      (period (depth + 1)) := by
  intro coordinate
  simp

private theorem boundary_succ_iff
    (side : FrameSide) (depth coordinate : Nat) :
    coordinate % period (depth + 1) = side.boundaryResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = side.boundaryResidue depth ∧
        coordinate % 4 = side.fineResidue := by
  let residue := coordinate % period (depth + 1)
  have residueLt : residue < period (depth + 1) :=
    Nat.mod_lt _ (pow_pos (by decide) _)
  rw [← (boundary_periodic side depth).map_mod_nat coordinate]
  rw [← (boundaryLiftCondition_periodic side depth).map_mod_nat coordinate]
  change residue % period (depth + 1) = side.boundaryResidue (depth + 1) ↔
    ceilDivFour residue % period depth = side.boundaryResidue depth ∧
      residue % 4 = side.fineResidue
  rw [Nat.mod_eq_of_lt residueLt]
  have periodEq := period_succ depth
  have coarseLe : ceilDivFour residue ≤ period depth := by
    unfold ceilDivFour
    rw [periodEq] at residueLt
    omega
  by_cases coarseLt : ceilDivFour residue < period depth
  · rw [Nat.mod_eq_of_lt coarseLt]
    cases side with
    | opening =>
        simp only [FrameSide.boundaryResidue, FrameSide.fineResidue]
        rw [frameStartResidue_succ]
        have startPositive : 0 < frameStartResidue depth := by
          simp [frameStartResidue]
        unfold ceilDivFour
        omega
    | closing =>
        simp only [FrameSide.boundaryResidue, FrameSide.fineResidue]
        rw [frameEndResidue_succ]
        unfold ceilDivFour
        omega
  · have coarseEq : ceilDivFour residue = period depth := by omega
    have boundaryPositive := side.boundaryResidue_pos depth
    have boundaryLt := side.boundaryResidue_lt_period depth
    constructor
    · intro left
      have ceilEq : ceilDivFour residue = side.boundaryResidue depth := by
        rw [left]
        exact side.ceilDivFour_boundaryResidue_succ depth
      exact ((Nat.ne_of_gt boundaryLt) (coarseEq.symm.trans ceilEq)).elim
    · rintro ⟨right, _⟩
      rw [coarseEq, Nat.mod_self] at right
      exact ((Nat.ne_of_gt boundaryPositive) right.symm).elim

theorem openingBoundary_succ_iff (depth coordinate : Nat) :
    coordinate % period (depth + 1) = frameStartResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameStartResidue depth ∧
        coordinate % 4 = 1 := by
  simpa [FrameSide.boundaryResidue, FrameSide.fineResidue] using
    boundary_succ_iff .opening depth coordinate

theorem closingBoundary_succ_iff (depth coordinate : Nat) :
    coordinate % period (depth + 1) = frameEndResidue (depth + 1) ↔
      ceilDivFour coordinate % period depth = frameEndResidue depth ∧
        coordinate % 4 = 0 := by
  simpa [FrameSide.boundaryResidue, FrameSide.fineResidue] using
    boundary_succ_iff .closing depth coordinate

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

/- A deeper frame boundary projects to residue zero or one at every shallower
scale.  Shallower frame boundaries lie strictly beyond those residues, so no
point can belong to frame boundaries of two different depths.  The persistent
outer opening at coordinate one is disjoint for the same reason. -/

theorem period_dvd_scale_of_lt {small large : Nat} (h : small < large) :
    period small ∣ scale large := by
  rw [period, scale]
  exact Nat.pow_dvd_pow 4 (by omega)

private theorem largeBoundary_mod_small (side : FrameSide)
    {small large coordinate : Nat} (h : small < large)
    (boundary : coordinate % period large = side.boundaryResidue large) :
    coordinate % period small = side.fineResidue := by
  have periodDvd : period small ∣ period large := by
    rw [period, period]
    exact Nat.pow_dvd_pow 4 (by omega)
  have scaleDvd : period small ∣ scale large := period_dvd_scale_of_lt h
  calc
    coordinate % period small =
        (coordinate % period large) % period small :=
      (Nat.mod_mod_of_dvd coordinate periodDvd).symm
    _ = side.boundaryResidue large % period small := by rw [boundary]
    _ = side.fineResidue := by
      cases side with
      | opening =>
          rw [FrameSide.boundaryResidue, FrameSide.fineResidue,
            frameStartResidue, Nat.add_mod,
            Nat.mod_eq_zero_of_dvd scaleDvd]
          have oneLt : 1 < period small := by
            rw [period_eq_four_mul_scale]
            have := scale_pos small
            omega
          simp [Nat.mod_eq_of_lt oneLt]
      | closing =>
          rw [FrameSide.boundaryResidue, FrameSide.fineResidue,
            frameEndResidue, Nat.mul_mod,
            Nat.mod_eq_zero_of_dvd scaleDvd]
          simp

theorem largeOpening_mod_small {small large coordinate : Nat}
    (h : small < large)
    (opening : coordinate % period large = frameStartResidue large) :
    coordinate % period small = 1 := by
  exact largeBoundary_mod_small .opening h opening

theorem largeClosing_mod_small {small large coordinate : Nat}
    (h : small < large)
    (closing : coordinate % period large = frameEndResidue large) :
    coordinate % period small = 0 := by
  exact largeBoundary_mod_small .closing h closing

theorem outerBorder_lift (coordinate transverse : Nat) :
    liftBorder coordinate
        (outerBorder (ceilDivFour coordinate) (ceilDivFour transverse)) =
      outerBorder coordinate transverse := by
  unfold outerBorder ceilDivFour
  by_cases hcoarse : (coordinate + 3) / 4 = 1 ∧
      1 ≤ (transverse + 3) / 4
  · rw [if_pos hcoarse]
    have coordinateRange : 1 ≤ coordinate ∧ coordinate ≤ 4 := by omega
    have transversePositive : 1 ≤ transverse := by omega
    by_cases hcoordinate : coordinate = 1
    · simp [liftBorder, hcoordinate, transversePositive]
    · have coordinateMod : coordinate % 4 ≠ 1 := by omega
      simp [liftBorder, hcoordinate, coordinateMod]
  · rw [if_neg hcoarse]
    by_cases hfine : coordinate = 1 ∧ 1 ≤ transverse
    · exfalso
      apply hcoarse
      omega
    · simp [liftBorder, hfine]

theorem frameStartResidue_lt_frameEndResidue (depth : Nat) :
    frameStartResidue depth < frameEndResidue depth := by
  simp only [frameStartResidue, frameEndResidue]
  have := scale_pos depth
  omega

theorem frameBorder_eq_some_true_iff (depth coordinate transverse : Nat) :
    frameBorder depth coordinate transverse = some true ↔
      inFrame depth transverse = true ∧
        coordinate % period depth = frameStartResidue depth := by
  unfold frameBorder
  by_cases inside : inFrame depth transverse <;>
    by_cases opening : coordinate % period depth = frameStartResidue depth <;>
    simp [inside, opening]

theorem frameBorder_eq_some_false_iff (depth coordinate transverse : Nat) :
    frameBorder depth coordinate transverse = some false ↔
      inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  have distinct : frameStartResidue depth ≠ frameEndResidue depth :=
    (frameStartResidue_lt_frameEndResidue depth).ne
  unfold frameBorder
  by_cases inside : inFrame depth transverse
  · by_cases opening : coordinate % period depth = frameStartResidue depth
    · simp [inside, opening, distinct]
    · by_cases closing : coordinate % period depth = frameEndResidue depth <;>
        simp [inside, opening, closing, Ne.symm distinct]
  · simp [inside]

theorem frameBorders_disjoint_of_lt
    {small large coordinate transverse : Nat} (h : small < large)
    {smallOrientation largeOrientation : Bool}
    (smallBorder : frameBorder small coordinate transverse = some smallOrientation)
    (largeBorder : frameBorder large coordinate transverse = some largeOrientation) :
    False := by
  have largeResidue : coordinate % period small = 0 ∨
      coordinate % period small = 1 := by
    cases largeOrientation with
    | false =>
        left
        exact largeClosing_mod_small h
          ((frameBorder_eq_some_false_iff _ _ _).1 largeBorder).2
    | true =>
        right
        exact largeOpening_mod_small h
          ((frameBorder_eq_some_true_iff _ _ _).1 largeBorder).2
  have smallResidue : coordinate % period small = frameStartResidue small ∨
      coordinate % period small = frameEndResidue small := by
    cases smallOrientation with
    | false =>
        exact Or.inr ((frameBorder_eq_some_false_iff _ _ _).1 smallBorder).2
    | true =>
        exact Or.inl ((frameBorder_eq_some_true_iff _ _ _).1 smallBorder).2
  have startLarge : 1 < frameStartResidue small := by
    simp [frameStartResidue, scale_pos]
  have endLarge : 1 < frameEndResidue small := by
    simp only [frameEndResidue]
    have := scale_pos small
    omega
  rcases largeResidue with zero | one <;>
    rcases smallResidue with start | finish <;> omega

theorem outerBorder_frameBorder_disjoint
    {depth coordinate transverse : Nat} {outerOrientation frameOrientation : Bool}
    (outer : outerBorder coordinate transverse = some outerOrientation)
    (frame : frameBorder depth coordinate transverse = some frameOrientation) :
    False := by
  have coordinateOne : coordinate = 1 := by
    unfold outerBorder at outer
    split at outer
    · exact ‹coordinate = 1 ∧ 1 ≤ transverse›.1
    · simp at outer
  have oneLtPeriod : 1 < period depth := by
    rw [period_eq_four_mul_scale]
    have := scale_pos depth
    omega
  have coordinateMod : coordinate % period depth = 1 := by
    rw [coordinateOne, Nat.mod_eq_of_lt oneLtPeriod]
  have boundary : coordinate % period depth = frameStartResidue depth ∨
      coordinate % period depth = frameEndResidue depth := by
    cases frameOrientation with
    | false =>
        exact Or.inr ((frameBorder_eq_some_false_iff _ _ _).1 frame).2
    | true =>
        exact Or.inl ((frameBorder_eq_some_true_iff _ _ _).1 frame).2
  have startLarge : 1 < frameStartResidue depth := by
    simp [frameStartResidue, scale_pos]
  have endLarge : 1 < frameEndResidue depth := by
    simp only [frameEndResidue]
    have := scale_pos depth
    omega
  rcases boundary with start | finish <;> omega

theorem liftBorder_eq_some_imp
    {coordinate : Nat} {border : Option Bool} {orientation : Bool}
    (lifted : liftBorder coordinate border = some orientation) :
    border = some orientation := by
  cases border with
  | none => simp [liftBorder] at lifted
  | some value =>
      cases value <;> cases orientation <;> simp_all [liftBorder]

theorem firstBorder_eq_some_iff
    (first second : Option Bool) (orientation : Bool) :
    firstBorder first second = some orientation ↔
      first = some orientation ∨ (first = none ∧ second = some orientation) := by
  cases first <;> cases second <;> simp [firstBorder]

/- Because all candidate borders are pairwise disjoint, the executable
`Fin.findSome?` selector has the simple extensional description below.  Its
lifted form then separates the inherited depths `2 .. level + 1` from the new
depth-one frame used by the substitution recurrence. -/

/-- The finite selector contains exactly the outer opening and the frame
boundaries at depths `1` through `level`. -/
theorem selectedBorder_eq_some_iff
    (level coordinate transverse : Nat) (orientation : Bool) :
    selectedBorder level coordinate transverse = some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, 1 ≤ depth ∧ depth ≤ level ∧
          frameBorder depth coordinate transverse = some orientation := by
  rw [selectedBorder, Fin.findSome?_eq_some_iff]
  constructor
  · rintro ⟨index, candidate, _⟩
    by_cases zero : index.val = 0
    · left
      simpa [borderCandidate, zero] using candidate
    · right
      exact ⟨index.val, Nat.one_le_iff_ne_zero.2 zero,
        Nat.le_of_lt_succ index.isLt,
        by simpa [borderCandidate, zero] using candidate⟩
  · rintro (outer | ⟨depth, positive, bounded, border⟩)
    · refine ⟨⟨0, Nat.zero_lt_succ level⟩, ?_, ?_⟩
      · simpa [borderCandidate] using outer
      · intro prior priorLt
        exact (Nat.not_lt_zero prior.val priorLt).elim
    · refine ⟨⟨depth, by omega⟩, ?_, ?_⟩
      · simpa [borderCandidate, Nat.ne_of_gt positive] using border
      · intro prior priorLt
        by_cases zero : prior.val = 0
        · cases outerEq : outerBorder coordinate transverse with
          | none => simp [borderCandidate, zero, outerEq]
          | some outerOrientation =>
              exact (outerBorder_frameBorder_disjoint outerEq border).elim
        · cases priorEq : frameBorder prior.val coordinate transverse with
          | none => simp [borderCandidate, zero, priorEq]
          | some priorOrientation =>
              exact (frameBorders_disjoint_of_lt priorLt priorEq border).elim

theorem lift_selectedBorder_eq_some_iff
    (level coordinate transverse : Nat) (orientation : Bool) :
    liftBorder coordinate
        (selectedBorder level (ceilDivFour coordinate) (ceilDivFour transverse)) =
          some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, 2 ≤ depth ∧ depth ≤ level + 1 ∧
          frameBorder depth coordinate transverse = some orientation := by
  constructor
  · intro lifted
    have coarse := liftBorder_eq_some_imp lifted
    rcases (selectedBorder_eq_some_iff _ _ _ _).1 coarse with outer | frame
    · left
      rw [← outerBorder_lift]
      simpa only [outer, coarse] using lifted
    · rcases frame with ⟨depth, positive, bounded, border⟩
      right
      refine ⟨depth + 1, by omega, by omega, ?_⟩
      rw [← frameBorder_succ]
      simpa only [border, coarse] using lifted
  · rintro (outer | ⟨depth, depthLower, depthUpper, border⟩)
    · have coarseLift := outerBorder_lift coordinate transverse
      rw [outer] at coarseLift
      have coarseOuter := liftBorder_eq_some_imp coarseLift
      have coarseSelected := (selectedBorder_eq_some_iff level
        (ceilDivFour coordinate) (ceilDivFour transverse) orientation).2
        (Or.inl coarseOuter)
      simpa only [coarseSelected, coarseOuter] using coarseLift
    · obtain ⟨prior, depthEq⟩ : ∃ prior, depth = prior + 1 :=
        ⟨depth - 1, by omega⟩
      rw [depthEq] at depthLower depthUpper border
      rw [← frameBorder_succ prior coordinate transverse] at border
      have coarseBorder := liftBorder_eq_some_imp border
      have coarseSelected := (selectedBorder_eq_some_iff level
        (ceilDivFour coordinate) (ceilDivFour transverse) orientation).2
        (Or.inr ⟨prior, by omega, by omega, coarseBorder⟩)
      simpa only [coarseSelected, coarseBorder] using border

end ShadedCarrierBorderGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
