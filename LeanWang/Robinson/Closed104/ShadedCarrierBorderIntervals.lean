/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderGeometry

/-!
# Canonical intervals of the selected-border hierarchy

The recursive border factor contains the outer opening and every enclosing
Robinson frame boundary. Boundaries of different depths are disjoint, and a
larger frame boundary has residue zero or one modulo every smaller frame
period. Consequently no enclosing-frame boundary enters the interior of the
smallest frame owning a coordinate.

This identifies the opening and closing selected borders around every
arithmetic carrier cell and proves that both canonical signal edges of that
cell are clear.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierBorderGeometry

open ShadedCarrierHierarchy ShadedCarrierBorderHierarchy

/-- The persistent opening on the west or south side of every finite
supertile. -/
def outerBorder (coordinate transverse : Nat) : Option Bool :=
  if coordinate = 1 ∧ 1 ≤ transverse then some true else none

theorem period_dvd_scale_of_lt {small large : Nat} (h : small < large) :
    period small ∣ scale large := by
  rw [period, scale]
  exact Nat.pow_dvd_pow 4 (by omega)

/-- An opening boundary of a larger frame lies at residue one modulo every
smaller frame period. -/
theorem largeOpening_mod_small {small large coordinate : Nat}
    (h : small < large)
    (opening : coordinate % period large = frameStartResidue large) :
    coordinate % period small = 1 := by
  have periodDvd : period small ∣ period large := by
    rw [period, period]
    exact Nat.pow_dvd_pow 4 (by omega)
  have scaleDvd : period small ∣ scale large := period_dvd_scale_of_lt h
  calc
    coordinate % period small =
        (coordinate % period large) % period small :=
      (Nat.mod_mod_of_dvd coordinate periodDvd).symm
    _ = frameStartResidue large % period small := by rw [opening]
    _ = 1 := by
      rw [frameStartResidue, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd scaleDvd]
      have oneLt : 1 < period small := by
        rw [period_eq_four_mul_scale]
        have := scale_pos small
        omega
      simp [Nat.mod_eq_of_lt oneLt]

/-- A closing boundary of a larger frame lies at residue zero modulo every
smaller frame period. -/
theorem largeClosing_mod_small {small large coordinate : Nat}
    (h : small < large)
    (closing : coordinate % period large = frameEndResidue large) :
    coordinate % period small = 0 := by
  have periodDvd : period small ∣ period large := by
    rw [period, period]
    exact Nat.pow_dvd_pow 4 (by omega)
  have scaleDvd : period small ∣ scale large := period_dvd_scale_of_lt h
  calc
    coordinate % period small =
        (coordinate % period large) % period small :=
      (Nat.mod_mod_of_dvd coordinate periodDvd).symm
    _ = frameEndResidue large % period small := by rw [closing]
    _ = 0 := by
      rw [frameEndResidue, Nat.mul_mod,
        Nat.mod_eq_zero_of_dvd scaleDvd]
      simp

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

/-- No coordinate can be a boundary of two different frame depths. -/
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

/-- The recursive selector contains exactly the outer opening and the frame
boundaries at depths `1` through `level`. -/
theorem selectedBorder_eq_some_iff
    (level coordinate transverse : Nat) (orientation : Bool) :
    selectedBorder level coordinate transverse = some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, 1 ≤ depth ∧ depth ≤ level ∧
          frameBorder depth coordinate transverse = some orientation := by
  induction level generalizing coordinate transverse orientation with
  | zero =>
      simp [selectedBorder, outerBorder]
  | succ level inductionHypothesis =>
      rw [selectedBorder, firstBorder_eq_some_iff]
      constructor
      · rintro (oldLifted | ⟨_, newLifted⟩)
        · have old := liftBorder_eq_some_imp oldLifted
          rcases (inductionHypothesis _ _ _).1 old with outer | frame
          · left
            calc
              outerBorder coordinate transverse =
                  liftBorder coordinate
                    (outerBorder (ceilDivFour coordinate)
                      (ceilDivFour transverse)) :=
                (outerBorder_lift coordinate transverse).symm
              _ = liftBorder coordinate
                    (selectedBorder level (ceilDivFour coordinate)
                      (ceilDivFour transverse)) :=
                congrArg (liftBorder coordinate) (outer.trans old.symm)
              _ = some orientation := oldLifted
          · rcases frame with ⟨depth, positive, bounded, border⟩
            right
            refine ⟨depth + 1, by omega, by omega, ?_⟩
            rw [← frameBorder_succ depth coordinate transverse]
            rw [border.trans old.symm]
            exact oldLifted
        · right
          refine ⟨1, by omega, by omega, ?_⟩
          rw [← frameBorder_succ 0 coordinate transverse]
          exact newLifted
      · rintro (outer | frame)
        · left
          have coarseLift : liftBorder coordinate
              (outerBorder (ceilDivFour coordinate)
                (ceilDivFour transverse)) = some orientation := by
            rw [outerBorder_lift]
            exact outer
          have coarseOuter := liftBorder_eq_some_imp coarseLift
          have coarseSelected := (inductionHypothesis _ _ _).2 (Or.inl coarseOuter)
          rw [coarseSelected.trans coarseOuter.symm]
          exact coarseLift
        · rcases frame with ⟨depth, positive, bounded, border⟩
          cases depth with
          | zero => omega
          | succ prior =>
              cases prior with
              | zero =>
                  right
                  constructor
                  · by_contra oldNotNone
                    cases oldEq : liftBorder coordinate
                        (selectedBorder level (ceilDivFour coordinate)
                          (ceilDivFour transverse)) with
                    | none => exact oldNotNone oldEq
                    | some oldOrientation =>
                        have oldSelected := liftBorder_eq_some_imp oldEq
                        rcases (inductionHypothesis _ _ _).1 oldSelected with
                          coarseOuter | coarseFrame
                        · have fineOuter : outerBorder coordinate transverse =
                              some oldOrientation := by
                            calc
                              outerBorder coordinate transverse =
                                  liftBorder coordinate
                                    (outerBorder (ceilDivFour coordinate)
                                      (ceilDivFour transverse)) :=
                                (outerBorder_lift coordinate transverse).symm
                              _ = liftBorder coordinate
                                    (selectedBorder level (ceilDivFour coordinate)
                                      (ceilDivFour transverse)) :=
                                congrArg (liftBorder coordinate)
                                  (coarseOuter.trans oldSelected.symm)
                              _ = some oldOrientation := oldEq
                          exact outerBorder_frameBorder_disjoint fineOuter border
                        · rcases coarseFrame with
                            ⟨coarseDepth, coarsePositive, _, coarseBorder⟩
                          have fineBorder : frameBorder (coarseDepth + 1)
                              coordinate transverse = some oldOrientation := by
                            rw [← frameBorder_succ coarseDepth coordinate transverse]
                            rw [coarseBorder.trans oldSelected.symm]
                            exact oldEq
                          exact frameBorders_disjoint_of_lt
                            (show 1 < coarseDepth + 1 by omega) border fineBorder
                  · rw [← frameBorder_succ 0 coordinate transverse] at border
                    exact border
              | succ coarseDepth =>
                  left
                  have coarseLift : liftBorder coordinate
                      (frameBorder (coarseDepth + 1)
                        (ceilDivFour coordinate) (ceilDivFour transverse)) =
                        some orientation := by
                    rw [frameBorder_succ]
                    exact border
                  have coarseBorder := liftBorder_eq_some_imp coarseLift
                  have coarseSelected := (inductionHypothesis _ _ _).2
                    (Or.inr ⟨coarseDepth + 1, by omega, by omega, coarseBorder⟩)
                  rw [coarseSelected.trans coarseBorder.symm]
                  exact coarseLift

/-- A selected closing border is exactly a closing boundary of one of the
contributing frame depths.  The outer border contributes only an opening. -/
theorem selectedBorder_eq_some_false_iff
    (level coordinate transverse : Nat) :
    selectedBorder level coordinate transverse = some false ↔
      ∃ depth, 1 ≤ depth ∧ depth ≤ level ∧
        inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  rw [selectedBorder_eq_some_iff]
  simp [outerBorder, frameBorder_eq_some_false_iff]

private theorem ownerDepth_le_of_inFrame
    {level ownerDepth depth transverse : Nat}
    (owner : depthAt (level - 1) transverse = some ownerDepth)
    (positive : 1 ≤ depth)
    (inside : inFrame depth transverse = true) : ownerDepth ≤ depth := by
  by_contra smaller
  have withinSearch : depth ≤ level - 1 := by
    have ownerBound := depthAt_le owner
    omega
  have ownerLe := depthAt_le_of_inFrame owner positive withinSearch inside
  omega

/-- Once the smallest frame containing the transverse coordinate is known,
every selected frame boundary comes from that depth or a larger one. -/
theorem selectedBorder_eq_some_iff_of_owner
    {level ownerDepth coordinate transverse : Nat} {orientation : Bool}
    (owner : depthAt (level - 1) transverse = some ownerDepth) :
    selectedBorder level coordinate transverse = some orientation ↔
      outerBorder coordinate transverse = some orientation ∨
        ∃ depth, ownerDepth ≤ depth ∧ depth ≤ level ∧
          frameBorder depth coordinate transverse = some orientation := by
  rw [selectedBorder_eq_some_iff]
  constructor
  · rintro (outer | ⟨depth, positive, bounded, border⟩)
    · exact Or.inl outer
    · have inside : inFrame depth transverse = true := by
        cases orientation with
        | false => exact ((frameBorder_eq_some_false_iff _ _ _).1 border).1
        | true => exact ((frameBorder_eq_some_true_iff _ _ _).1 border).1
      exact Or.inr ⟨depth,
        ownerDepth_le_of_inFrame owner positive inside,
        bounded, border⟩
  · rintro (outer | ⟨depth, ownerLe, bounded, border⟩)
    · exact Or.inl outer
    · exact Or.inr ⟨depth, (depthAt_pos owner).trans_le ownerLe,
        bounded, border⟩

/-- Closing-border normal form relative to the smallest containing frame. -/
theorem selectedBorder_eq_some_false_iff_of_owner
    {level ownerDepth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some ownerDepth) :
    selectedBorder level coordinate transverse = some false ↔
      ∃ depth, ownerDepth ≤ depth ∧ depth ≤ level ∧
        inFrame depth transverse = true ∧
        coordinate % period depth = frameEndResidue depth := by
  rw [selectedBorder_eq_some_false_iff]
  constructor
  · rintro ⟨depth, positive, bounded, inside, closing⟩
    exact ⟨depth, ownerDepth_le_of_inFrame owner positive inside,
      bounded, inside, closing⟩
  · rintro ⟨depth, ownerLe, bounded, inside, closing⟩
    exact ⟨depth, (depthAt_pos owner).trans_le ownerLe,
      bounded, inside, closing⟩

/-- No selected boundary of any enclosing frame enters the strict interior of
the smallest frame owning the transverse coordinate. -/
theorem selectedBorder_eq_none_of_owner_interior
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (inside : inFrame depth coordinate = true)
    (interior : onFrameBoundary depth coordinate = false) :
    selectedBorder level coordinate transverse = none := by
  cases borderEq : selectedBorder level coordinate transverse with
  | none => rfl
  | some orientation =>
      rcases (selectedBorder_eq_some_iff_of_owner owner).1 borderEq with
        outer | frame
      · have coordinateOne : coordinate = 1 := by
          unfold outerBorder at outer
          split at outer
          · exact ‹coordinate = 1 ∧ 1 ≤ transverse›.1
          · simp at outer
        have insideData :
            frameStartResidue depth ≤ coordinate % period depth ∧
              coordinate % period depth ≤ frameEndResidue depth := by
          simpa only [inFrame, Bool.and_eq_true, decide_eq_true_eq] using inside
        have oneLtPeriod : 1 < period depth := by
          rw [period_eq_four_mul_scale]
          have := scale_pos depth
          omega
        have coordinateMod : coordinate % period depth = 1 := by
          rw [coordinateOne, Nat.mod_eq_of_lt oneLtPeriod]
        have startLarge : 1 < frameStartResidue depth := by
          simp [frameStartResidue, scale_pos]
        omega
      · rcases frame with ⟨frameDepth, depthLeFrame, _, frame⟩
        rcases depthLeFrame.eq_or_lt with equal | less
        · subst frameDepth
          have boundary : onFrameBoundary depth coordinate = true := by
            cases orientation with
            | false =>
                have closing :=
                  ((frameBorder_eq_some_false_iff _ _ _).1 frame).2
                simp [onFrameBoundary, closing]
            | true =>
                have opening :=
                  ((frameBorder_eq_some_true_iff _ _ _).1 frame).2
                simp [onFrameBoundary, opening]
          simp [boundary] at interior
        · have largeResidue : coordinate % period depth = 0 ∨
              coordinate % period depth = 1 := by
            cases orientation with
            | false =>
                exact Or.inl (largeClosing_mod_small less
                  ((frameBorder_eq_some_false_iff _ _ _).1 frame).2)
            | true =>
                exact Or.inr (largeOpening_mod_small less
                  ((frameBorder_eq_some_true_iff _ _ _).1 frame).2)
          have insideData :
              frameStartResidue depth ≤ coordinate % period depth ∧
                coordinate % period depth ≤ frameEndResidue depth := by
            simpa only [inFrame, Bool.and_eq_true, decide_eq_true_eq] using inside
          have startLarge : 1 < frameStartResidue depth := by
            simp [frameStartResidue, scale_pos]
          rcases largeResidue with zero | one <;> omega

/-- Start of the frame-period block containing `coordinate`. -/
def frameBase (depth coordinate : Nat) : Nat :=
  period depth * (coordinate / period depth)

def frameOpening (depth coordinate : Nat) : Nat :=
  frameBase depth coordinate + frameStartResidue depth

def frameClosing (depth coordinate : Nat) : Nat :=
  frameBase depth coordinate + frameEndResidue depth

theorem frameBase_add_mod (depth coordinate : Nat) :
    frameBase depth coordinate + coordinate % period depth = coordinate := by
  unfold frameBase
  have decomposition := Nat.mod_add_div coordinate (period depth)
  omega

theorem frameBase_le (depth coordinate : Nat) :
    frameBase depth coordinate ≤ coordinate := by
  have decomposition := frameBase_add_mod depth coordinate
  omega

theorem coordinate_lt_frameBase_add_period (depth coordinate : Nat) :
    coordinate < frameBase depth coordinate + period depth := by
  have decomposition := frameBase_add_mod depth coordinate
  have periodPositive : 0 < period depth := by
    rw [period_eq_four_mul_scale]
    exact Nat.mul_pos (by decide) (scale_pos depth)
  have residueLt := Nat.mod_lt coordinate periodPositive
  omega

theorem mod_eq_sub_frameBase_of_mem_block
    {depth reference coordinate : Nat}
    (lower : frameBase depth reference ≤ coordinate)
    (upper : coordinate < frameBase depth reference + period depth) :
    coordinate % period depth = coordinate - frameBase depth reference := by
  let base := frameBase depth reference
  have offsetLt : coordinate - base < period depth := by
    omega
  have baseMod : base % period depth = 0 := by
    simp [base, frameBase]
  calc
    coordinate % period depth =
        (base + (coordinate - base)) % period depth := by
      rw [Nat.add_sub_of_le lower]
    _ = (base % period depth +
        (coordinate - base) % period depth) % period depth := by
      rw [Nat.add_mod]
    _ = coordinate - base := by
      rw [baseMod, Nat.mod_eq_of_lt offsetLt]
      simp [Nat.mod_eq_of_lt offsetLt]

theorem frameOpening_mod (depth coordinate : Nat) :
    frameOpening depth coordinate % period depth = frameStartResidue depth := by
  have startLt : frameStartResidue depth < period depth :=
    (frameStartResidue_lt_frameEndResidue depth).trans
      (frameEndResidue_lt_period depth)
  simp [frameOpening, frameBase, Nat.add_mod, Nat.mod_eq_of_lt startLt]

theorem frameClosing_mod (depth coordinate : Nat) :
    frameClosing depth coordinate % period depth = frameEndResidue depth := by
  simp [frameClosing, frameBase, Nat.add_mod,
    Nat.mod_eq_of_lt (frameEndResidue_lt_period depth)]

theorem frameOpening_lt_frameClosing (depth coordinate : Nat) :
    frameOpening depth coordinate < frameClosing depth coordinate := by
  simp only [frameOpening, frameClosing]
  exact Nat.add_lt_add_left
    (frameStartResidue_lt_frameEndResidue depth) _

theorem between_frameBounds
    {depth coordinate position : Nat}
    (afterOpening : frameOpening depth coordinate < position)
    (beforeClosing : position < frameClosing depth coordinate) :
    inFrame depth position = true ∧ onFrameBoundary depth position = false := by
  let base := frameBase depth coordinate
  have baseLe : base ≤ position := by
    simp only [frameOpening] at afterOpening
    omega
  have offsetLt : position - base < period depth := by
    simp only [frameClosing] at beforeClosing
    have endLt := frameEndResidue_lt_period depth
    omega
  have baseMod : base % period depth = 0 := by
    simp [base, frameBase]
  have positionMod : position % period depth = position - base := by
    calc
      position % period depth = (base + (position - base)) % period depth := by
        rw [Nat.add_sub_of_le baseLe]
      _ = (base % period depth +
          (position - base) % period depth) % period depth := by
        rw [Nat.add_mod]
      _ = position - base := by
        rw [baseMod, Nat.mod_eq_of_lt offsetLt]
        simp [Nat.mod_eq_of_lt offsetLt]
  have startLt : frameStartResidue depth < position - base := by
    simp only [frameOpening] at afterOpening
    omega
  have beforeEnd : position - base < frameEndResidue depth := by
    simp only [frameClosing] at beforeClosing
    omega
  constructor
  · simp [inFrame, positionMod]
    omega
  · simp [onFrameBoundary, positionMod]
    omega

theorem selectedBorder_frameOpening
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    selectedBorder level (frameOpening depth coordinate) transverse = some true := by
  apply (selectedBorder_eq_some_iff _ _ _ _).2
  right
  refine ⟨depth, depthAt_pos owner, ?_, ?_⟩
  · have := depthAt_le owner
    omega
  · apply (frameBorder_eq_some_true_iff _ _ _).2
    exact ⟨inFrame_eq_true_of_depthAt_eq_some owner,
      frameOpening_mod depth coordinate⟩

theorem selectedBorder_frameClosing
    {level depth coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    selectedBorder level (frameClosing depth coordinate) transverse = some false := by
  apply (selectedBorder_eq_some_iff _ _ _ _).2
  right
  refine ⟨depth, depthAt_pos owner, ?_, ?_⟩
  · have := depthAt_le owner
    omega
  · apply (frameBorder_eq_some_false_iff _ _ _).2
    exact ⟨inFrame_eq_true_of_depthAt_eq_some owner,
      frameClosing_mod depth coordinate⟩

theorem selectedBorder_none_between_frameBounds
    {level depth coordinate transverse position : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (afterOpening : frameOpening depth coordinate < position)
    (beforeClosing : position < frameClosing depth coordinate) :
    selectedBorder level position transverse = none := by
  have geometry := between_frameBounds afterOpening beforeClosing
  exact selectedBorder_eq_none_of_owner_interior owner geometry.1 geometry.2

theorem previousInterior_eq_opening
    {interior : Nat → Option Bool} {opening closing position : Nat}
    (openingBorder : interior opening = some true)
    (between : ∀ candidate, opening < candidate → candidate < closing →
      interior candidate = none)
    (afterOpening : opening < position) (atMostClosing : position ≤ closing) :
    ShadedSignalRectangle.previousInterior interior position = some true := by
  have startLe : opening + 1 ≤ position := by omega
  induction position, startLe using Nat.le_induction with
  | base =>
      simp [ShadedSignalRectangle.previousInterior, openingBorder]
  | succ position _ inductionHypothesis =>
      have positionBetween : opening < position ∧ position < closing := by omega
      have previous := inductionHypothesis positionBetween.1 (by omega)
      simp [ShadedSignalRectangle.previousInterior,
        between position positionBetween.1 positionBetween.2, previous]

theorem previousInterior_eq_closing
    {interior : Nat → Option Bool} {closing position : Nat}
    (closingBorder : interior closing = some false)
    (between : ∀ candidate, closing < candidate → candidate < position →
      interior candidate = none)
    (afterClosing : closing < position) :
    ShadedSignalRectangle.previousInterior interior position = some false := by
  have startLe : closing + 1 ≤ position := by omega
  induction position, startLe using Nat.le_induction with
  | base =>
      simp [ShadedSignalRectangle.previousInterior, closingBorder]
  | succ position _ inductionHypothesis =>
      have positionBetween : closing < position ∧ position < position + 1 := by
        omega
      have previous := inductionHypothesis
        (fun candidate lower upper => between candidate lower (by omega))
        positionBetween.1
      simp [ShadedSignalRectangle.previousInterior,
        between position positionBetween.1 positionBetween.2, previous]

theorem nextInterior_eq_closing
    {interior : Nat → Option Bool} {position closing length : Nat}
    (closingBorder : interior closing = some false)
    (between : ∀ candidate, position ≤ candidate → candidate < closing →
      interior candidate = none)
    (atMostClosing : position ≤ closing) (closingBeforeEnd : closing < length) :
    ShadedSignalRectangle.nextInterior interior position (length - position) =
      some false := by
  induction distance : closing - position generalizing position with
  | zero =>
      have positionEq : position = closing := by omega
      subst position
      have fuelPositive : 0 < length - closing := by omega
      obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero fuelPositive.ne'
      rw [fuelEq]
      simp [ShadedSignalRectangle.nextInterior, closingBorder]
  | succ distance inductionHypothesis =>
      have positionBefore : position < closing := by omega
      have fuelEq : length - position = length - (position + 1) + 1 := by omega
      rw [fuelEq]
      simp only [ShadedSignalRectangle.nextInterior,
        between position (by omega) positionBefore]
      apply inductionHypothesis (position := position + 1)
      · intro candidate lower upper
        exact between candidate (by omega) upper
      · omega
      · omega

theorem nextInterior_eq_true_of_no_false_before
    {interior : Nat → Option Bool} {position opening length : Nat}
    (openingBorder : interior opening = some true)
    (noClosing : ∀ candidate, position ≤ candidate → candidate < opening →
      interior candidate ≠ some false)
    (atMostOpening : position ≤ opening)
    (openingBeforeEnd : opening < length) :
    ShadedSignalRectangle.nextInterior interior position (length - position) =
      some true := by
  induction distance : opening - position generalizing position with
  | zero =>
      have positionEq : position = opening := by omega
      subst position
      have fuelPositive : 0 < length - opening := by omega
      obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero fuelPositive.ne'
      rw [fuelEq]
      simp [ShadedSignalRectangle.nextInterior, openingBorder]
  | succ distance inductionHypothesis =>
      have positionBefore : position < opening := by omega
      have fuelEq : length - position = length - (position + 1) + 1 := by omega
      rw [fuelEq]
      cases current : interior position with
      | none =>
          simp only [ShadedSignalRectangle.nextInterior, current]
          apply inductionHypothesis (position := position + 1)
          · intro candidate lower upper
            exact noClosing candidate (by omega) upper
          · omega
          · omega
      | some orientation =>
          cases orientation with
          | false => exact (noClosing position le_rfl positionBefore current).elim
          | true => simp [ShadedSignalRectangle.nextInterior, current]

theorem exists_interior_of_nextInterior_eq_some
    {interior : Nat → Option Bool} {position fuel : Nat}
    {orientation : Bool}
    (next : ShadedSignalRectangle.nextInterior interior position fuel =
      some orientation) :
    ∃ candidate, position ≤ candidate ∧ candidate < position + fuel ∧
      interior candidate = some orientation := by
  induction fuel generalizing position with
  | zero => simp [ShadedSignalRectangle.nextInterior] at next
  | succ fuel inductionHypothesis =>
      cases current : interior position with
      | none =>
          simp only [ShadedSignalRectangle.nextInterior, current] at next
          obtain ⟨candidate, lower, upper, selected⟩ := inductionHypothesis next
          exact ⟨candidate, by omega, by omega, selected⟩
      | some currentOrientation =>
          simp only [ShadedSignalRectangle.nextInterior, current] at next
          cases next
          exact ⟨position, le_rfl, by omega, current⟩

/-- A clear canonical edge lies strictly between a witnessed opening and
closing border when no closing intervenes before the opening and no border
intervenes after the closing. -/
theorem between_borders_of_intervalEdge_eq_none
    {interior : Nat → Option Bool} {opening closing position length : Nat}
    (clear : ShadedSignalRectangle.intervalEdge interior length position = .none)
    (positionClear : interior position = none)
    (openingBorder : interior opening = some true)
    (closingBorder : interior closing = some false)
    (openingBeforeClosing : opening < closing)
    (closingBeforeEnd : closing < length)
    (noClosingBeforeOpening : ∀ candidate, position ≤ candidate →
      candidate < opening → interior candidate ≠ some false)
    (noBorderAfterClosing : ∀ candidate, closing < candidate →
      candidate < position → interior candidate = none) :
    opening < position ∧ position < closing := by
  have edgeData := (ShadedSignalRectangle.intervalEdge_eq_none_iff
    interior length position).1 clear
  constructor
  · rcases Nat.lt_trichotomy position opening with before | equal | after
    · have nextTrue : ShadedSignalRectangle.nextInterior interior position
          (length - position) = some true := by
        apply nextInterior_eq_true_of_no_false_before openingBorder
          noClosingBeforeOpening before.le
          (openingBeforeClosing.trans closingBeforeEnd)
      rw [nextTrue] at edgeData
      simp at edgeData
    · subst opening
      rw [positionClear] at openingBorder
      simp at openingBorder
    · exact after
  · rcases Nat.lt_trichotomy position closing with before | equal | after
    · exact before
    · subst closing
      rw [positionClear] at closingBorder
      simp at closingBorder
    · have previousFalse :
          ShadedSignalRectangle.previousInterior interior position =
            some false := by
        exact previousInterior_eq_closing closingBorder noBorderAfterClosing after
      exact (edgeData.2 previousFalse).elim

theorem selectedBorder_ne_some_false_before_frameOpening
    {level depth coordinate transverse candidate : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (coordinateClear : selectedBorder level coordinate transverse = none)
    (lower : coordinate ≤ candidate)
    (beforeOpening : candidate < frameOpening depth coordinate) :
    selectedBorder level candidate transverse ≠ some false := by
  intro selected
  rcases (selectedBorder_eq_some_false_iff_of_owner owner).1 selected with
    ⟨frameDepth, depthLeFrame, _, _, closing⟩
  have baseLe : frameBase depth coordinate ≤ candidate :=
      (frameBase_le depth coordinate).trans lower
  have openingBeforeBlockEnd : frameOpening depth coordinate <
        frameBase depth coordinate + period depth := by
      simp only [frameOpening]
      exact Nat.add_lt_add_left
        ((frameStartResidue_lt_frameEndResidue depth).trans
          (frameEndResidue_lt_period depth)) _
  have candidateMod : candidate % period depth =
        candidate - frameBase depth coordinate :=
      mod_eq_sub_frameBase_of_mem_block baseLe
        (beforeOpening.trans openingBeforeBlockEnd)
  rcases depthLeFrame.eq_or_lt with equal | larger
  · subst frameDepth
    have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth
    simp only [frameOpening] at beforeOpening
    omega
  · have largeResidue : candidate % period depth = 0 :=
      largeClosing_mod_small larger closing
    have coordinateBaseLe := frameBase_le depth coordinate
    have candidateEq : candidate = frameBase depth coordinate := by omega
    have coordinateEq : coordinate = candidate := by omega
    rw [← coordinateEq, coordinateClear] at selected
    simp at selected

theorem selectedBorder_eq_none_after_frameClosing
    {level depth coordinate transverse candidate : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (afterClosing : frameClosing depth coordinate < candidate)
    (beforeCoordinate : candidate < coordinate) :
    selectedBorder level candidate transverse = none := by
  cases selected : selectedBorder level candidate transverse with
  | none => rfl
  | some orientation =>
      rcases (selectedBorder_eq_some_iff_of_owner owner).1 selected with
        outer | frame
      · have candidateOne : candidate = 1 := by
          unfold outerBorder at outer
          split at outer
          · exact ‹candidate = 1 ∧ 1 ≤ transverse›.1
          · simp at outer
        have closingLarge : 1 < frameClosing depth coordinate := by
          simp only [frameClosing, frameEndResidue]
          have := scale_pos depth
          omega
        omega
      · rcases frame with ⟨frameDepth, depthLeFrame, _, border⟩
        have frameResidue : candidate % period frameDepth =
              frameStartResidue frameDepth ∨
            candidate % period frameDepth = frameEndResidue frameDepth := by
          cases orientation with
          | false =>
              exact Or.inr ((frameBorder_eq_some_false_iff _ _ _).1 border).2
          | true =>
              exact Or.inl ((frameBorder_eq_some_true_iff _ _ _).1 border).2
        have baseLe : frameBase depth coordinate ≤ candidate := by
          simp only [frameClosing] at afterClosing
          omega
        have candidateUpper : candidate <
            frameBase depth coordinate + period depth :=
          beforeCoordinate.trans
            (coordinate_lt_frameBase_add_period depth coordinate)
        have candidateMod : candidate % period depth =
            candidate - frameBase depth coordinate :=
          mod_eq_sub_frameBase_of_mem_block baseLe candidateUpper
        have afterEnd : frameEndResidue depth < candidate % period depth := by
          simp only [frameClosing] at afterClosing
          omega
        rcases depthLeFrame.eq_or_lt with equal | larger
        · subst frameDepth
          have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth
          rcases frameResidue with opening | closing <;> omega
        · have largeResidue : candidate % period depth = 0 ∨
              candidate % period depth = 1 := by
            rcases frameResidue with opening | closing
            · exact Or.inr (largeOpening_mod_small larger opening)
            · exact Or.inl (largeClosing_mod_small larger closing)
          have endLarge : 1 < frameEndResidue depth := by
            simp only [frameEndResidue]
            have := scale_pos depth
            omega
          rcases largeResidue with zero | one <;> omega

theorem selectedBorder_ne_some_false_of_no_owner
    {level coordinate transverse : Nat}
    (owner : depthAt (level - 1) transverse = none)
    (coordinate_lt : coordinate < 2 * scale level) :
    selectedBorder level coordinate transverse ≠ some false := by
  intro selected
  rcases (selectedBorder_eq_some_false_iff level coordinate transverse).1
      selected with ⟨depth, positive, bounded, inside, closing⟩
  by_cases withinSearch : depth ≤ level - 1
  · have outside := inFrame_eq_false_of_depthAt_eq_none owner
      positive withinSearch
    simp [inside] at outside
  · have depthEq : depth = level := by omega
    subst depth
    have residueLe := Nat.mod_le coordinate (period level)
    rw [closing] at residueLe
    simp only [frameEndResidue] at residueLe
    have := scale_pos level
    omega

theorem period_dvd_two_mul_scale {depth level : Nat} (hdepth : depth < level) :
    period depth ∣ 2 * scale level :=
  dvd_mul_of_dvd_right (period_dvd_scale_of_lt hdepth) 2

theorem frameClosing_lt_two_mul_scale
    {depth level coordinate : Nat} (hdepth : depth < level)
    (coordinate_lt : coordinate < 2 * scale level) :
    frameClosing depth coordinate < 2 * scale level := by
  have periodPositive : 0 < period depth := by
    rw [period_eq_four_mul_scale]
    have := scale_pos depth
    omega
  have lengthDvd := period_dvd_two_mul_scale hdepth
  have quotientLt : coordinate / period depth <
      (2 * scale level) / period depth := by
    apply (Nat.div_lt_iff_lt_mul periodPositive).2
    rw [Nat.mul_comm, Nat.mul_div_cancel' lengthDvd]
    exact coordinate_lt
  have nextBlockLe : period depth * (coordinate / period depth + 1) ≤
      2 * scale level := by
    have multiplied := Nat.mul_le_mul_left (period depth)
      (Nat.succ_le_iff.2 quotientLt)
    rw [Nat.mul_div_cancel' lengthDvd] at multiplied
    exact multiplied
  have closingBeforeNext : frameClosing depth coordinate <
      period depth * (coordinate / period depth + 1) := by
    have endLt := frameEndResidue_lt_period depth
    simpa [frameClosing, frameBase, Nat.mul_add] using
      Nat.add_lt_add_left endLt (period depth * (coordinate / period depth))
  exact closingBeforeNext.trans_le nextBlockLe

/-- Every arithmetic horizontal carrier cell has clear canonical signal on
both horizontal edges for the actual recursive selected-border sequence. -/
theorem intervalEdge_pair_of_horizontalCarrier
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < 2 * scale level)
    (carrier : isHorizontalCarrier level coordinate transverse = true) :
    ShadedSignalRectangle.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) coordinate = .none ∧
      ShadedSignalRectangle.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) (coordinate + 1) = .none := by
  cases owner : depthAt (level - 1) transverse with
  | none => simp [isHorizontalCarrier, owner] at carrier
  | some depth =>
      have carrierData : inFrame depth coordinate = true ∧
          onFrameBoundary depth coordinate = false := by
        simpa [isHorizontalCarrier, owner] using carrier
      have insideData :
          frameStartResidue depth ≤ coordinate % period depth ∧
            coordinate % period depth ≤ frameEndResidue depth := by
        simpa only [inFrame, Bool.and_eq_true, decide_eq_true_eq] using
          carrierData.1
      have interiorData :
          coordinate % period depth ≠ frameStartResidue depth ∧
            coordinate % period depth ≠ frameEndResidue depth := by
        simpa only [onFrameBoundary,
          Bool.or_eq_false_eq_eq_false_and_eq_false,
          decide_eq_false_iff_not] using carrierData.2
      have decomposition := frameBase_add_mod depth coordinate
      have openingBefore : frameOpening depth coordinate < coordinate := by
        unfold frameOpening
        omega
      have beforeClosing : coordinate < frameClosing depth coordinate := by
        unfold frameClosing
        omega
      have successorAtMostClosing : coordinate + 1 ≤
          frameClosing depth coordinate := by omega
      have depth_lt_level : depth < level := by
        have depthBound := depthAt_le owner
        have levelPositive : 0 < level := by
          by_contra levelZero
          have : level = 0 := Nat.eq_zero_of_not_pos levelZero
          subst level
          simp at owner
        exact depthBound.trans_lt (Nat.sub_lt levelPositive (by decide))
      have closingBeforeEnd := frameClosing_lt_two_mul_scale
        depth_lt_level coordinate_lt
      have openingBorder := selectedBorder_frameOpening
        (coordinate := coordinate) owner
      have closingBorder := selectedBorder_frameClosing
        (coordinate := coordinate) owner
      have noBorder := fun candidate (after : frameOpening depth coordinate < candidate)
          (before : candidate < frameClosing depth coordinate) =>
        selectedBorder_none_between_frameBounds owner after before
      have previous (position : Nat)
          (after : frameOpening depth coordinate < position)
          (before : position ≤ frameClosing depth coordinate) :
          ShadedSignalRectangle.previousInterior
              (fun x => selectedBorder level x transverse) position = some true :=
        previousInterior_eq_opening openingBorder noBorder after before
      have next (position : Nat)
          (lower : coordinate ≤ position)
          (before : position ≤ frameClosing depth coordinate) :
          ShadedSignalRectangle.nextInterior
              (fun x => selectedBorder level x transverse) position
                (2 * scale level - position) = some false := by
        apply nextInterior_eq_closing
            (interior := fun x => selectedBorder level x transverse)
            (position := position)
            (closing := frameClosing depth coordinate)
            (length := 2 * scale level) closingBorder
            (atMostClosing := before) (closingBeforeEnd := closingBeforeEnd)
        intro candidate candidateLower candidateBefore
        exact noBorder candidate (by omega) candidateBefore
      constructor
      · rw [ShadedSignalRectangle.intervalEdge_eq_none_iff]
        exact ⟨next coordinate (by omega) (by omega), by
          rw [previous coordinate openingBefore (by omega)]
          simp⟩
      · rw [ShadedSignalRectangle.intervalEdge_eq_none_iff]
        exact ⟨next (coordinate + 1) (by omega) successorAtMostClosing, by
          rw [previous (coordinate + 1) (by omega) successorAtMostClosing]
          simp⟩

/-- Conversely, the canonical signal can be clear on both sides of a cell only
inside the smallest frame owning its row. -/
theorem horizontalCarrier_of_intervalEdge_pair
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < 2 * scale level)
    (clear :
      ShadedSignalRectangle.intervalEdge
            (fun x => selectedBorder level x transverse)
            (2 * scale level) coordinate = .none ∧
        ShadedSignalRectangle.intervalEdge
            (fun x => selectedBorder level x transverse)
            (2 * scale level) (coordinate + 1) = .none) :
    isHorizontalCarrier level coordinate transverse = true := by
  let interior := fun x => selectedBorder level x transverse
  have coordinateClear : interior coordinate = none :=
    ShadedSignalRectangle.interior_eq_none_of_adjacent_clear
      interior coordinate_lt clear.1 clear.2
  have coordinateClear' : selectedBorder level coordinate transverse = none := by
    simpa [interior] using coordinateClear
  have edgeData := (ShadedSignalRectangle.intervalEdge_eq_none_iff
    interior (2 * scale level) coordinate).1 clear.1
  cases owner : depthAt (level - 1) transverse with
  | none =>
      obtain ⟨candidate, lower, upper, selected⟩ :=
        exists_interior_of_nextInterior_eq_some edgeData.1
      have candidate_lt : candidate < 2 * scale level := by
        have coordinateLe : coordinate ≤ 2 * scale level := coordinate_lt.le
        simpa [Nat.add_sub_of_le coordinateLe] using upper
      exact (selectedBorder_ne_some_false_of_no_owner owner candidate_lt
        selected).elim
  | some depth =>
      have depth_lt_level : depth < level := by
        have depthBound := depthAt_le owner
        have levelPositive : 0 < level := by
          by_contra levelZero
          have : level = 0 := Nat.eq_zero_of_not_pos levelZero
          subst level
          simp at owner
        exact depthBound.trans_lt (Nat.sub_lt levelPositive (by decide))
      have closingBeforeEnd := frameClosing_lt_two_mul_scale
        depth_lt_level coordinate_lt
      have openingBorder := selectedBorder_frameOpening
        (level := level) (coordinate := coordinate) owner
      have closingBorder := selectedBorder_frameClosing
        (level := level) (coordinate := coordinate) owner
      have bounds := between_borders_of_intervalEdge_eq_none
        clear.1 coordinateClear
        (by simpa [interior] using openingBorder)
        (by simpa [interior] using closingBorder)
        (frameOpening_lt_frameClosing depth coordinate) closingBeforeEnd
        (fun candidate lower before =>
          selectedBorder_ne_some_false_before_frameOpening owner
            coordinateClear' lower before)
        (fun candidate after before =>
          selectedBorder_eq_none_after_frameClosing owner after before)
      have decomposition := frameBase_add_mod depth coordinate
      have geometry : inFrame depth coordinate = true ∧
          onFrameBoundary depth coordinate = false := by
        constructor
        · simp [inFrame]
          simp only [frameOpening, frameClosing] at bounds
          omega
        · simp [onFrameBoundary]
          simp only [frameOpening, frameClosing] at bounds
          omega
      simpa [isHorizontalCarrier, owner] using geometry

theorem intervalEdge_pair_iff_horizontalCarrier
    {level coordinate transverse : Nat}
    (coordinate_lt : coordinate < 2 * scale level) :
    (ShadedSignalRectangle.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) coordinate = .none ∧
      ShadedSignalRectangle.intervalEdge
          (fun x => selectedBorder level x transverse)
          (2 * scale level) (coordinate + 1) = .none) ↔
      isHorizontalCarrier level coordinate transverse = true := by
  constructor
  · exact horizontalCarrier_of_intervalEdge_pair coordinate_lt
  · exact intervalEdge_pair_of_horizontalCarrier coordinate_lt

end ShadedCarrierBorderGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
