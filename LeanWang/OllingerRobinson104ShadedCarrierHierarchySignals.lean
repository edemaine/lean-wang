/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierHierarchy
import LeanWang.OllingerRobinson104ShadedSignalRectangle

/-!
# Explicit signals for the shaded carrier hierarchy

The selected border at a row or column is the boundary of its smallest
containing frame.  A finite supertile also has an outer opening border at
coordinate one and one unclosed frame at its current depth.  The explicit
flow below is clear exactly between the opening and closing borders of a
completed frame.  This avoids any search through the finite border sequence.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierHierarchySignals

open ShadedCarrierHierarchy

/-- Selected border predicted at one cell of a level-`level` finite
supertile.  `true` is an opening and `false` is a closing border. -/
def selectedBorder (level coordinate transverse : Nat) : Option Bool :=
  if coordinate = 1 ∧ 1 ≤ transverse then some true
  else
    match depthAt level transverse with
    | none => none
    | some depth =>
        if coordinate % period depth = frameStartResidue depth then some true
        else if coordinate % period depth = frameEndResidue depth then some false
        else none

/-- Edge positions strictly after an opening and at or before its matching
closing border. -/
def isClearEdge (depth position : Nat) : Bool :=
  frameStartResidue depth < position % period depth &&
    position % period depth ≤ frameEndResidue depth

/-- Explicit flow on one hierarchy row or column. -/
def edge (level transverse position : Nat) : Signals.Flow :=
  if transverse = 0 then .backward
  else if position ≤ 1 then .forward
  else
    match depthAt (level - 1) transverse with
    | none => .backward
    | some depth => if isClearEdge depth position then .none else .backward

theorem period_pos (depth : Nat) : 0 < period depth := by
  rw [period_eq_four_mul_scale]
  exact Nat.mul_pos (by decide) (scale_pos depth)

theorem frameStartResidue_lt_frameEndResidue (depth : Nat)
    (positive : 0 < depth) :
    frameStartResidue depth < frameEndResidue depth := by
  simp only [frameStartResidue, frameEndResidue]
  have scale_ge_four : 4 ≤ scale depth := by
    rcases depth with _ | depth
    · omega
    have positivePower : 0 < 4 ^ depth := pow_pos (by decide) depth
    simp only [scale, pow_succ]
    omega
  omega

theorem two_lt_frameStartResidue (depth : Nat) (positive : 0 < depth) :
    2 < frameStartResidue depth := by
  simp only [frameStartResidue]
  have scale_ge_four : 4 ≤ scale depth := by
    rcases depth with _ | depth
    · omega
    have positivePower : 0 < 4 ^ depth := pow_pos (by decide) depth
    simp only [scale, pow_succ]
    omega
  omega

private theorem successor_mod_of_succ_lt
    {depth coordinate : Nat}
    (residueSuccLt : coordinate % period depth + 1 < period depth) :
    (coordinate + 1) % period depth = coordinate % period depth + 1 := by
  have oneLt : 1 < period depth := by
    rw [period_eq_four_mul_scale]
    have positive := scale_pos depth
    omega
  calc
    (coordinate + 1) % period depth =
        (coordinate % period depth + 1 % period depth) % period depth := by
          rw [Nat.add_mod]
    _ = (coordinate % period depth + 1) % period depth := by
          rw [Nat.mod_eq_of_lt oneLt]
    _ = coordinate % period depth + 1 := Nat.mod_eq_of_lt residueSuccLt

@[simp] theorem isClearEdge_at_start
    (depth coordinate : Nat)
    (start : coordinate % period depth = frameStartResidue depth) :
    isClearEdge depth coordinate = false := by
  simp [isClearEdge, start]

@[simp] theorem isClearEdge_after_start
    (depth coordinate : Nat) (positive : 0 < depth)
    (start : coordinate % period depth = frameStartResidue depth) :
    isClearEdge depth (coordinate + 1) = true := by
  have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth positive
  have residueSuccLt : coordinate % period depth + 1 < period depth := by
    rw [start]
    exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.2 startBeforeEnd)
      (frameEndResidue_lt_period depth)
  rw [isClearEdge, successor_mod_of_succ_lt residueSuccLt, start]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

@[simp] theorem isClearEdge_at_end
    (depth coordinate : Nat) (positive : 0 < depth)
    (finish : coordinate % period depth = frameEndResidue depth) :
    isClearEdge depth coordinate = true := by
  have startBeforeEnd := frameStartResidue_lt_frameEndResidue depth positive
  simp [isClearEdge, finish, startBeforeEnd]

@[simp] theorem isClearEdge_after_end
    (depth coordinate : Nat) (positive : 0 < depth)
    (finish : coordinate % period depth = frameEndResidue depth) :
    isClearEdge depth (coordinate + 1) = false := by
  have endLt := frameEndResidue_lt_period depth
  have scalePositive := scale_pos depth
  have startLarge := two_lt_frameStartResidue depth positive
  have endSuccLt : frameEndResidue depth + 1 < period depth := by
    rw [frameStartResidue] at startLarge
    rw [frameEndResidue, period_eq_four_mul_scale]
    omega
  have successorMod :
      (coordinate + 1) % period depth = frameEndResidue depth + 1 := by
    rw [successor_mod_of_succ_lt (finish ▸ endSuccLt), finish]
  simp [isClearEdge, successorMod]

theorem isClearEdge_succ_eq_of_not_boundary
    (depth coordinate : Nat)
    (notStart : coordinate % period depth ≠ frameStartResidue depth)
    (notEnd : coordinate % period depth ≠ frameEndResidue depth) :
    isClearEdge depth (coordinate + 1) = isClearEdge depth coordinate := by
  by_cases beforeStart : coordinate % period depth < frameStartResidue depth
  · have nextLeStart : coordinate % period depth + 1 ≤ frameStartResidue depth := by
      omega
    have beforeEnd : coordinate % period depth < frameEndResidue depth :=
      beforeStart.trans (by
        simp only [frameStartResidue, frameEndResidue]
        have positive := scale_pos depth
        omega)
    have residueSuccLt : coordinate % period depth + 1 < period depth :=
      Nat.lt_of_le_of_lt (Nat.succ_le_iff.2 beforeEnd)
        (frameEndResidue_lt_period depth)
    rw [isClearEdge, isClearEdge,
      successor_mod_of_succ_lt residueSuccLt]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · by_cases beforeEnd : coordinate % period depth < frameEndResidue depth
    · have residueSuccLt : coordinate % period depth + 1 < period depth :=
        Nat.lt_of_le_of_lt (Nat.succ_le_iff.2 beforeEnd)
          (frameEndResidue_lt_period depth)
      rw [isClearEdge, isClearEdge,
        successor_mod_of_succ_lt residueSuccLt]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    · have endLe : frameEndResidue depth ≤ coordinate % period depth := by omega
      have currentFalse : isClearEdge depth coordinate = false := by
        apply Bool.eq_false_iff.mpr
        intro currentClear
        have currentData :
            frameStartResidue depth < coordinate % period depth ∧
              coordinate % period depth ≤ frameEndResidue depth := by
          simpa only [isClearEdge, Bool.and_eq_true, decide_eq_true_eq] using
            currentClear
        omega
      rw [currentFalse]
      apply Bool.eq_false_iff.2
      intro successorClear
      have successorData :
          frameStartResidue depth < (coordinate + 1) % period depth ∧
            (coordinate + 1) % period depth ≤ frameEndResidue depth := by
        simpa [isClearEdge] using successorClear
      have periodPositive := period_pos depth
      have residueLt := Nat.mod_lt coordinate periodPositive
      by_cases residueSuccLt : coordinate % period depth + 1 < period depth
      · have successorMod := successor_mod_of_succ_lt residueSuccLt
        rw [successorMod] at successorData
        omega
      · have residueEq : coordinate % period depth + 1 = period depth := by
          omega
        have oneLt : 1 < period depth := by
          rw [period_eq_four_mul_scale]
          have positive := scale_pos depth
          omega
        have wrapped : (coordinate + 1) % period depth = 0 := by
          calc
            (coordinate + 1) % period depth =
                (coordinate % period depth + 1 % period depth) % period depth := by
                  rw [Nat.add_mod]
            _ = (coordinate % period depth + 1) % period depth := by
                  rw [Nat.mod_eq_of_lt oneLt]
            _ = period depth % period depth := by rw [residueEq]
            _ = 0 := Nat.mod_self _
        rw [wrapped] at successorData
        have startPositive : 0 < frameStartResidue depth := by
          simp [frameStartResidue]
        omega

@[simp] theorem depthAt_coordinate_zero (level : Nat) :
    depthAt level 0 = none := by
  induction level with
  | zero => rfl
  | succ level inductionHypothesis =>
      simp only [depthAt, inductionHypothesis]
      rw [if_neg]
      simp [inFrame, frameStartResidue]

theorem isClearEdge_two_eq_false (depth : Nat) (positive : 0 < depth) :
    isClearEdge depth 2 = false := by
  have twoLtStart := two_lt_frameStartResidue depth positive
  have twoLtPeriod : 2 < period depth :=
    twoLtStart.trans (frameStartResidue_lt_frameEndResidue depth positive) |>.trans
      (frameEndResidue_lt_period depth)
  rw [isClearEdge, Nat.mod_eq_of_lt twoLtPeriod]
  simp
  omega

/-- The explicit hierarchy edge assignment satisfies the selected-border
flow rule at every cell of the finite supertile. -/
theorem flowAllowed_edge (level coordinate transverse : Nat)
    (coordinate_lt : coordinate < 2 * scale level) :
    ShadedSignalRectangle.flowAllowed
      (selectedBorder level coordinate transverse)
      (edge level transverse coordinate)
      (edge level transverse (coordinate + 1)) = true := by
  by_cases transverseZero : transverse = 0
  · subst transverse
    simp [selectedBorder, edge, ShadedSignalRectangle.flowAllowed]
  have transversePositive : 1 ≤ transverse := by omega
  by_cases coordinateZero : coordinate = 0
  · subst coordinate
    cases owner : depthAt level transverse with
    | none =>
        simp [selectedBorder, edge, transverseZero, owner,
          ShadedSignalRectangle.flowAllowed]
    | some depth =>
        have depthPositive := depthAt_pos owner
        have startPositive : 0 < frameStartResidue depth := by
          simp [frameStartResidue]
        have endPositive : 0 < frameEndResidue depth := by
          simp [frameEndResidue, scale_pos]
        simp [selectedBorder, edge, transverseZero, owner,
          ShadedSignalRectangle.flowAllowed, startPositive.ne,
          endPositive.ne]
  by_cases coordinateOne : coordinate = 1
  · subst coordinate
    cases owner : depthAt (level - 1) transverse with
    | none =>
        simp [selectedBorder, edge, transverseZero, transversePositive, owner,
          ShadedSignalRectangle.flowAllowed]
    | some depth =>
        have depthPositive := depthAt_pos owner
        have clearTwo := isClearEdge_two_eq_false depth depthPositive
        simp [selectedBorder, edge, transverseZero, transversePositive, owner,
          clearTwo, ShadedSignalRectangle.flowAllowed]
  have coordinateLarge : ¬coordinate ≤ 1 := by omega
  have successorLarge : ¬coordinate + 1 ≤ 1 := by omega
  cases previousOwner : depthAt (level - 1) transverse with
  | some depth =>
      have currentOwner : depthAt level transverse = some depth :=
        depthAt_eq_some_mono previousOwner (Nat.sub_le level 1)
      have depthPositive := depthAt_pos previousOwner
      by_cases start :
          coordinate % period depth = frameStartResidue depth
      · have afterClear := isClearEdge_after_start depth coordinate
          depthPositive start
        simp [selectedBorder, coordinateOne, currentOwner, start,
          edge, transverseZero, coordinateLarge, successorLarge,
          previousOwner, afterClear,
          ShadedSignalRectangle.flowAllowed]
      · by_cases finish :
            coordinate % period depth = frameEndResidue depth
        · have beforeClear := isClearEdge_at_end depth coordinate
            depthPositive finish
          have afterClear := isClearEdge_after_end depth coordinate
            depthPositive finish
          have endNotStart :
              frameEndResidue depth ≠ frameStartResidue depth :=
            (frameStartResidue_lt_frameEndResidue depth depthPositive).ne'
          simp [selectedBorder, coordinateOne, currentOwner, finish,
            edge, transverseZero, coordinateLarge, successorLarge,
            previousOwner, beforeClear, afterClear, endNotStart,
            ShadedSignalRectangle.flowAllowed]
        · have sameClear := isClearEdge_succ_eq_of_not_boundary
            depth coordinate start finish
          simp [selectedBorder, coordinateOne, currentOwner, start, finish,
            edge, transverseZero, coordinateLarge, successorLarge,
            previousOwner, sameClear, ShadedSignalRectangle.flowAllowed]
  | none =>
      cases currentOwner : depthAt level transverse with
      | none =>
          simp [selectedBorder, coordinateOne, currentOwner,
            edge, transverseZero, coordinateLarge, successorLarge,
            previousOwner, ShadedSignalRectangle.flowAllowed]
      | some depth =>
          have depthPositive := depthAt_pos currentOwner
          have depthLe := depthAt_le currentOwner
          have notPrevious : ¬depth ≤ level - 1 := by
            intro depthLePrevious
            have outside := inFrame_eq_false_of_depthAt_eq_none previousOwner
              depthPositive depthLePrevious
            have inside := inFrame_eq_true_of_depthAt_eq_some currentOwner
            simp [inside] at outside
          have depthEq : depth = level := by omega
          have scalePositive := scale_pos level
          have coordinateBeforeEnd :
              coordinate < frameEndResidue depth := by
            rw [depthEq, frameEndResidue]
            omega
          have notFinish :
              coordinate % period depth ≠ frameEndResidue depth := by
            intro finish
            have residueLe := Nat.mod_le coordinate (period depth)
            rw [finish] at residueLe
            omega
          by_cases start :
              coordinate % period depth = frameStartResidue depth
          · simp [selectedBorder, coordinateOne, currentOwner, start,
              edge, transverseZero, coordinateLarge, successorLarge,
              previousOwner, ShadedSignalRectangle.flowAllowed]
          · simp [selectedBorder, coordinateOne, currentOwner, start, notFinish,
              edge, transverseZero, coordinateLarge, successorLarge,
              previousOwner, ShadedSignalRectangle.flowAllowed]

theorem clearEdge_pair_iff (depth position : Nat) (positive : 0 < depth) :
    isClearEdge depth position = true ∧
        isClearEdge depth (position + 1) = true ↔
      inFrame depth position = true ∧
        onFrameBoundary depth position = false := by
  constructor
  · rintro ⟨currentClear, nextClear⟩
    have currentData :
        frameStartResidue depth < position % period depth ∧
          position % period depth ≤ frameEndResidue depth := by
      simpa only [isClearEdge, Bool.and_eq_true, decide_eq_true_eq] using
        currentClear
    have notEnd :
        position % period depth ≠ frameEndResidue depth := by
      intro finish
      have afterEnd := isClearEdge_after_end depth position positive finish
      rw [afterEnd] at nextClear
      contradiction
    constructor
    · simpa only [inFrame, Bool.and_eq_true, decide_eq_true_eq] using
        ⟨currentData.1.le, currentData.2⟩
    · simp only [onFrameBoundary,
        Bool.or_eq_false_eq_eq_false_and_eq_false,
        decide_eq_false_iff_not]
      exact ⟨currentData.1.ne', notEnd⟩
  · rintro ⟨inside, interior⟩
    have insideData :
        frameStartResidue depth ≤ position % period depth ∧
          position % period depth ≤ frameEndResidue depth := by
      simpa only [inFrame, Bool.and_eq_true, decide_eq_true_eq] using inside
    have interiorData :
        position % period depth ≠ frameStartResidue depth ∧
          position % period depth ≠ frameEndResidue depth := by
      simpa only [onFrameBoundary,
        Bool.or_eq_false_eq_eq_false_and_eq_false,
        decide_eq_false_iff_not] using interior
    have startLt :
        frameStartResidue depth < position % period depth := by omega
    have beforeEnd :
        position % period depth < frameEndResidue depth := by omega
    have residueSuccLt : position % period depth + 1 < period depth :=
      Nat.lt_of_le_of_lt (Nat.succ_le_iff.2 beforeEnd)
        (frameEndResidue_lt_period depth)
    have successorMod := successor_mod_of_succ_lt residueSuccLt
    constructor
    · simpa only [isClearEdge, Bool.and_eq_true, decide_eq_true_eq] using
        ⟨startLt, insideData.2⟩
    · rw [isClearEdge, successorMod]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

/-- A cell has two clear hierarchy edges exactly when the row or column owner
frame carries through that nonboundary cell. -/
theorem edge_pair_iff_carrier (level position transverse : Nat) :
    edge level transverse position = .none ∧
        edge level transverse (position + 1) = .none ↔
      isHorizontalCarrier level position transverse = true := by
  cases owner : depthAt (level - 1) transverse with
  | none =>
      have noClear (candidate : Nat) :
          edge level transverse candidate ≠ .none := by
        by_cases transverseZero : transverse = 0
        · simp [edge, transverseZero]
        · by_cases candidateSmall : candidate ≤ 1
          · simp [edge, transverseZero, candidateSmall]
          · simp [edge, transverseZero, candidateSmall, owner]
      constructor
      · rintro ⟨leftClear, _⟩
        exact (noClear position leftClear).elim
      · intro carrier
        simp [isHorizontalCarrier, owner] at carrier
  | some depth =>
      have depthPositive := depthAt_pos owner
      have transverseNonzero : transverse ≠ 0 := by
        intro transverseZero
        subst transverse
        simp at owner
      by_cases positionSmall : position ≤ 1
      · have positionCases : position = 0 ∨ position = 1 := by omega
        rcases positionCases with rfl | rfl
        · have notInside : inFrame depth 0 = false := by
            simp [inFrame, frameStartResidue]
          simp [edge, transverseNonzero, owner, isHorizontalCarrier,
            notInside]
        · have clearTwo := isClearEdge_two_eq_false depth depthPositive
          have oneLtPeriod : 1 < period depth := by
            exact (show 1 < 2 by decide).trans
              ((two_lt_frameStartResidue depth depthPositive).trans
                (frameStartResidue_lt_frameEndResidue depth depthPositive) |>.trans
                  (frameEndResidue_lt_period depth))
          have oneMod : 1 % period depth = 1 :=
            Nat.mod_eq_of_lt oneLtPeriod
          have notInside : inFrame depth 1 = false := by
            have startLarge := two_lt_frameStartResidue depth depthPositive
            simp only [inFrame, oneMod, Bool.and_eq_false_eq_eq_false_or_eq_false]
            simp only [decide_eq_false_iff_not]
            left
            omega
          simp [edge, transverseNonzero, owner, clearTwo,
            isHorizontalCarrier, notInside]
      · have successorLarge : ¬position + 1 ≤ 1 := by omega
        have left :
            edge level transverse position = .none ↔
              isClearEdge depth position = true := by
          simp [edge, transverseNonzero, positionSmall, owner]
        have right :
            edge level transverse (position + 1) = .none ↔
              isClearEdge depth (position + 1) = true := by
          simp [edge, transverseNonzero, successorLarge, owner]
        rw [left, right, clearEdge_pair_iff depth position depthPositive]
        simp [isHorizontalCarrier, owner]

/-- Two-dimensional signal state obtained by using the explicit hierarchy
edge independently in each row and column. -/
def signalGrid (level : Nat) : Nat → Nat → Signals.State := fun x y =>
  { west := edge level y x
    east := edge level y (x + 1)
    south := edge level x y
    north := edge level x (y + 1) }

@[simp] theorem signalGrid_west (level x y : Nat) :
    (signalGrid level x y).west = edge level y x := rfl

@[simp] theorem signalGrid_east (level x y : Nat) :
    (signalGrid level x y).east = edge level y (x + 1) := rfl

@[simp] theorem signalGrid_south (level x y : Nat) :
    (signalGrid level x y).south = edge level x y := rfl

@[simp] theorem signalGrid_north (level x y : Nat) :
    (signalGrid level x y).north = edge level x (y + 1) := rfl

/-- Once a concrete shade rectangle has the predicted selected borders, the
explicit hierarchy signals give a valid decorated signal rectangle. -/
theorem validSignalRectangle_of_selectedBorders
    (level : Nat) (indexGrid : Nat → Nat → Index)
    (shadeGrid : Nat → Nat → RedShades.State)
    (shadeValid : RedShadeGraphColoring.ValidShadeRectangle
      indexGrid shadeGrid (2 * scale level) (2 * scale level))
    (horizontal : ∀ x y, x < 2 * scale level → y < 2 * scale level →
      ShadedSignalRectangle.horizontalInterior indexGrid shadeGrid x y =
        selectedBorder level x y)
    (vertical : ∀ x y, x < 2 * scale level → y < 2 * scale level →
      ShadedSignalRectangle.verticalInterior indexGrid shadeGrid x y =
        selectedBorder level y x) :
    ShadedSignalRectangle.ValidSignalRectangle indexGrid shadeGrid
      (signalGrid level) (2 * scale level) (2 * scale level) := by
  constructor
  · exact shadeValid
  · intro x y hx hy
    have horizontalFlow := flowAllowed_edge level x y hx
    have verticalFlow := flowAllowed_edge level y x hy
    rw [← horizontal x y hx hy] at horizontalFlow
    rw [← vertical x y hx hy] at verticalFlow
    simp only [ShadedSignalRectangle.horizontalInterior,
      ShadedSignalRectangle.flowAllowed_horizontal] at horizontalFlow
    simp only [ShadedSignalRectangle.verticalInterior,
      ShadedSignalRectangle.flowAllowed_vertical] at verticalFlow
    rw [ShadedSignals.locallyAllowed, Bool.and_eq_true]
    simp only [ShadedSignals.selectedVerticalInterior?,
      ShadedSignals.selectedHorizontalInterior?]
    constructor
    · rw [ShadedSignalRectangle.horizontalAllowed_only_horizontal,
        signalGrid_west, signalGrid_east]
      exact horizontalFlow
    · rw [ShadedSignalRectangle.verticalAllowed_only_vertical,
        signalGrid_south, signalGrid_north]
      exact verticalFlow
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl

theorem horizontal_clear_iff (level x y : Nat) :
    (signalGrid level x y).west = .none ∧
        (signalGrid level x y).east = .none ↔
      isHorizontalCarrier level x y = true := by
  exact edge_pair_iff_carrier level x y

theorem vertical_clear_iff (level x y : Nat) :
    (signalGrid level x y).south = .none ∧
        (signalGrid level x y).north = .none ↔
      isVerticalCarrier level x y = true := by
  simpa only [signalGrid_south, signalGrid_north, isVerticalCarrier,
    isHorizontalCarrier] using
    (show edge level x y = .none ∧ edge level x (y + 1) = .none ↔
        isHorizontalCarrier level y x = true from
      edge_pair_iff_carrier level y x)

end ShadedCarrierHierarchySignals
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
