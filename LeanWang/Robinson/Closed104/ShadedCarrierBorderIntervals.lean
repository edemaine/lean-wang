/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderGeometry

/-!
# Canonical intervals of the selected-border hierarchy

The finite border selector contains the outer opening and every enclosing
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
        apply ShadedSignalRectangle.nextInterior_eq_of_no_opposite_before
          openingBorder
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
        exact ShadedSignalRectangle.previousInterior_eq_of_none_between
          closingBorder noBorderAfterClosing after
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
both horizontal edges for the actual selected-border sequence. -/
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
        ShadedSignalRectangle.previousInterior_eq_of_none_between
          openingBorder (fun candidate lower upper =>
            noBorder candidate lower (upper.trans_le before)) after
      have next (position : Nat)
          (lower : coordinate ≤ position)
          (before : position ≤ frameClosing depth coordinate) :
          ShadedSignalRectangle.nextInterior
              (fun x => selectedBorder level x transverse) position
                (2 * scale level - position) = some false := by
        apply ShadedSignalRectangle.nextInterior_eq_of_no_opposite_before
            (interior := fun x => selectedBorder level x transverse)
            (position := position)
            (border := frameClosing depth coordinate)
            (length := 2 * scale level) closingBorder
            (atMostBorder := before) (borderBeforeEnd := closingBeforeEnd)
        intro candidate candidateLower candidateBefore
        rw [noBorder candidate (by omega) candidateBefore]
        simp
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
        ShadedSignalRectangle.exists_interior_of_nextInterior_eq_some edgeData.1
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
