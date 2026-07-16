/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierConcreteRoles
import LeanWang.OllingerRobinson104ShadedCarrierHierarchyAddressing

/-!
# Centered corner markers in canonical shaded supertiles

The thin layer fixes the parity phase of every corrected tile. In one
two-substitution block, corrected index `0` is either inherited at local
position `(0, 0)` or newly created at `(2, 2)`. The new copy lies on a frame
boundary; an inherited all-clear copy either introduces the centered depth-one
crossing or lifts a centered crossing from the previous level.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierCornerAddressing

open ShadedCarrierHierarchy
open ShadedCarrierBorderGeometry
open ShadedCarrierConcreteRoles
open ShadedCarrierHierarchyAddressing
open ShadedSubstitution
open ShadedSubstitutionPlane
open RedShadeGraphRefinement
open Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Checkerboard phase of the thin layer at a corrected-tile coordinate. -/
def thinPhase (x y : Nat) : Figure16.Thin :=
  if x % 2 = 0 then
    if y % 2 = 0 then .a else .d
  else if y % 2 = 0 then .c else .b

theorem thinPhase_eq_a_iff (x y : Nat) :
    thinPhase x y = .a ↔ x % 2 = 0 ∧ y % 2 = 0 := by
  have xCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have yCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases xCases with hx | hx <;> rcases yCases with hy | hy <;>
    simp [thinPhase, hx, hy]

theorem thinPhase_eq_b_iff (x y : Nat) :
    thinPhase x y = .b ↔ x % 2 = 1 ∧ y % 2 = 1 := by
  have xCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have yCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases xCases with hx | hx <;> rcases yCases with hy | hy <;>
    simp [thinPhase, hx, hy]

theorem quadrantAt_eq_northeast_iff (x y : Nat) :
    quadrantAt x y = .northeast ↔ x % 2 = 1 ∧ y % 2 = 1 := by
  have xCases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have yCases : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases xCases with hx | hx <;> rcases yCases with hy | hy <;>
    simp [quadrantAt, Quadrant.ofBits, hx, hy]

set_option linter.style.nativeDecide false in
theorem fineGrid_thinPhase (parent : Index) (x y : Fin 4) :
    (components (fineGrid parent x y)).1 = thinPhase x y := by
  revert parent x y
  native_decide

set_option linter.style.nativeDecide false in
theorem fineGrid_eq_zero_iff (parent : Index) (x y : Fin 4) :
    fineGrid parent x y = 0 ↔
      (x = 0 ∧ y = 0 ∧ (parent = 0 ∨ parent = 4)) ∨
      (x = 2 ∧ y = 2 ∧ (components parent).1 = .a) := by
  revert parent x y
  native_decide

set_option linter.style.nativeDecide false in
theorem components_zero_thin : (components (0 : Index)).1 = .a := by
  native_decide

set_option linter.style.nativeDecide false in
theorem components_four_thin : (components (4 : Index)).1 = .b := by
  native_decide

set_option linter.style.nativeDecide false in
theorem modelData_seed_parent :
    (modelData (encodeNode false 0)).map DecoratedData.parent = some 0 := by
  native_decide

theorem seedNode_parent : seedNode.data.parent = 0 := by
  have chosen := Node.modelData_data seedNode
  change modelData (encodeNode false 0) = some seedNode.data at chosen
  have seedParent := modelData_seed_parent
  rw [chosen] at seedParent
  exact Option.some.inj seedParent

theorem childPosition_mod_four (x y : Nat) :
    (childPosition x y : Nat) % 4 = x % 4 := by
  simp [childPosition, Nat.add_mod]

theorem childPosition_div_four (x y : Nat) :
    (childPosition x y : Nat) / 4 = y % 4 := by
  change (x % 4 + 4 * (y % 4)) / 4 = y % 4
  have := Nat.mod_lt x (by decide : 0 < 4)
  omega

theorem supertileIndexGrid_thinPhase
    (level x y : Nat) (hx : x < 4 ^ level) (hy : y < 4 ^ level) :
    (components (supertileIndexGrid level seedNode x y)).1 =
      thinPhase x y := by
  cases level with
  | zero =>
      have xZero : x = 0 := by simpa using hx
      have yZero : y = 0 := by simpa using hy
      subst x
      subst y
      simp [supertileIndexGrid, supertileNodeGrid, iterateNodeRefine,
        seedNode_parent, thinPhase, components_zero_thin]
  | succ level =>
      let parent := supertileNodeGrid level seedNode (x / 4) (y / 4)
      have localPhase := fineGrid_thinPhase parent.data.parent
        ⟨x % 4, Nat.mod_lt _ (by decide)⟩
        ⟨y % 4, Nat.mod_lt _ (by decide)⟩
      change (components
        ((parent.child (childPosition x y)).data.parent)).1 = _
      rw [Node.child_parent, childPosition_mod_four, childPosition_div_four]
      simpa [thinPhase, Nat.mod_mod] using localPhase

theorem even_coordinates_of_index_zero
    {level x y : Nat} (hx : x < 4 ^ level) (hy : y < 4 ^ level)
    (indexZero : supertileIndexGrid level seedNode x y = 0) :
    x % 2 = 0 ∧ y % 2 = 0 := by
  have phase := supertileIndexGrid_thinPhase level x y hx hy
  rw [indexZero, components_zero_thin] at phase
  exact (thinPhase_eq_a_iff x y).1 phase.symm

theorem odd_coordinates_of_index_four
    {level x y : Nat} (hx : x < 4 ^ level) (hy : y < 4 ^ level)
    (indexFour : supertileIndexGrid level seedNode x y = 4) :
    x % 2 = 1 ∧ y % 2 = 1 := by
  have phase := supertileIndexGrid_thinPhase level x y hx hy
  rw [indexFour, components_four_thin] at phase
  exact (thinPhase_eq_b_iff x y).1 phase.symm

/-- Fine quarter coordinate of an inherited northeast quarter. -/
def liftCoordinate (coordinate : Nat) : Nat := 4 * coordinate - 3

theorem liftCoordinate_pos {coordinate : Nat} (positive : 0 < coordinate) :
    0 < liftCoordinate coordinate := by
  unfold liftCoordinate
  omega

theorem ceilDivFour_liftCoordinate
    {coordinate : Nat} (positive : 0 < coordinate) :
    ShadedCarrierBorderHierarchy.ceilDivFour (liftCoordinate coordinate) =
      coordinate := by
  exact ceilDivFour_four_mul_sub_three coordinate positive

theorem liftCoordinate_mod_four
    {coordinate : Nat} (positive : 0 < coordinate) :
    liftCoordinate coordinate % 4 = 1 := by
  unfold liftCoordinate
  omega

theorem inFrame_succ_liftCoordinate
    (depth : Nat) {coordinate : Nat} (positive : 0 < coordinate) :
    inFrame (depth + 1) (liftCoordinate coordinate) =
      inFrame depth coordinate := by
  rw [inFrame_succ_iff_ceilDivFour,
    ceilDivFour_liftCoordinate positive]

theorem liftCoordinate_centerResidue
    {depth coordinate : Nat} (positive : 0 < coordinate)
    (center : coordinate % period depth = 2 * scale depth + 1) :
    liftCoordinate coordinate % period (depth + 1) =
      2 * scale (depth + 1) + 1 := by
  have decomposition := Nat.mod_add_div coordinate (period depth)
  have periodEq := period_succ depth
  have scaleEq : scale (depth + 1) = 4 * scale depth := by
    simp [scale, pow_succ, Nat.mul_comm]
  have coordinateEq : coordinate =
      2 * scale depth + 1 +
        period depth * (coordinate / period depth) := by
    omega
  have expression : liftCoordinate coordinate =
      period (depth + 1) * (coordinate / period depth) +
        (2 * scale (depth + 1) + 1) := by
    calc
      liftCoordinate coordinate = 4 * coordinate - 3 := rfl
      _ = 4 * (2 * scale depth + 1 +
          period depth * (coordinate / period depth)) - 3 := by
        exact congrArg (fun value => 4 * value - 3) coordinateEq
      _ = 4 * (period depth * (coordinate / period depth)) +
          (2 * (4 * scale depth) + 1) := by omega
      _ = period (depth + 1) * (coordinate / period depth) +
          (2 * scale (depth + 1) + 1) := by
        rw [periodEq, scaleEq, Nat.mul_assoc]
  have centerLt : 2 * scale (depth + 1) + 1 < period (depth + 1) := by
    rw [period_eq_four_mul_scale]
    have := scale_pos (depth + 1)
    omega
  rw [expression, Nat.add_mod]
  simp [Nat.mod_eq_of_lt centerLt]

/-- For coordinates at residue one modulo four, inherited positive-depth
frames shift up by one depth and no new depth-one owner is introduced. -/
theorem depthAt_liftCoordinate
    (bound coordinate : Nat) (positive : 0 < coordinate)
    (modOne : coordinate % 4 = 1) :
    depthAt (bound + 1) (liftCoordinate coordinate) =
      (depthAt bound coordinate).map (fun depth => depth + 1) := by
  induction bound with
  | zero =>
      simp only [depthAt, Option.map_none]
      rw [inFrame_succ_liftCoordinate 0 positive]
      simp [inFrame, period, scale, frameStartResidue,
        frameEndResidue, modOne]
  | succ bound inductionHypothesis =>
      change
        (match depthAt (bound + 1) (liftCoordinate coordinate) with
        | some depth => some depth
        | none =>
            if inFrame (bound + 2) (liftCoordinate coordinate) = true then
              some (bound + 2)
            else none) =
          Option.map (fun depth => depth + 1)
            (match depthAt bound coordinate with
            | some depth => some depth
            | none =>
                if inFrame (bound + 1) coordinate = true then
                  some (bound + 1)
                else none)
      rw [inductionHypothesis]
      cases previous : depthAt bound coordinate with
      | some depth => simp
      | none =>
          simp only [Option.map_none]
          rw [inFrame_succ_liftCoordinate (bound + 1) positive]
          by_cases inside : inFrame (bound + 1) coordinate <;>
            simp [inside]

theorem onFrameBoundary_eq_false_of_liftCoordinate
    {depth coordinate : Nat} (depthPositive : 0 < depth)
    (coordinatePositive : 0 < coordinate)
    (modOne : coordinate % 4 = 1)
    (fineInterior :
      onFrameBoundary (depth + 1) (liftCoordinate coordinate) = false) :
    onFrameBoundary depth coordinate = false := by
  have fineData :
      liftCoordinate coordinate % period (depth + 1) ≠
          frameStartResidue (depth + 1) ∧
        liftCoordinate coordinate % period (depth + 1) ≠
          frameEndResidue (depth + 1) := by
    simpa only [onFrameBoundary,
      Bool.or_eq_false_eq_eq_false_and_eq_false,
      decide_eq_false_iff_not] using fineInterior
  apply Bool.eq_false_iff.2
  intro boundary
  have coarseData : coordinate % period depth = frameStartResidue depth ∨
      coordinate % period depth = frameEndResidue depth := by
    simpa only [onFrameBoundary, Bool.or_eq_true,
      decide_eq_true_eq] using boundary
  rcases coarseData with opening | closing
  · apply fineData.1
    apply (openingBoundary_succ_iff depth (liftCoordinate coordinate)).2
    exact ⟨by simpa [ceilDivFour_liftCoordinate coordinatePositive] using opening,
      liftCoordinate_mod_four coordinatePositive⟩
  · have zeroResidue : coordinate % period 0 = 0 :=
      largeClosing_mod_small depthPositive closing
    have periodZero : period 0 = 4 := by simp [period]
    rw [periodZero, modOne] at zeroResidue
    contradiction

theorem horizontalCarrier_of_liftCoordinate
    {level x y : Nat} (levelPositive : 0 < level)
    (xPositive : 0 < x) (yPositive : 0 < y)
    (xMod : x % 4 = 1) (yMod : y % 4 = 1)
    (fineCarrier : isHorizontalCarrier (level + 1)
      (liftCoordinate x) (liftCoordinate y) = true) :
    isHorizontalCarrier level x y = true := by
  have rowShift : depthAt level (liftCoordinate y) =
      (depthAt (level - 1) y).map (fun depth => depth + 1) := by
    simpa [Nat.sub_add_cancel levelPositive] using
      depthAt_liftCoordinate (level - 1) y yPositive yMod
  cases owner : depthAt (level - 1) y with
  | none => simp [isHorizontalCarrier, rowShift, owner] at fineCarrier
  | some depth =>
      have fineData : inFrame (depth + 1) (liftCoordinate x) = true ∧
          onFrameBoundary (depth + 1) (liftCoordinate x) = false := by
        simpa [isHorizontalCarrier, rowShift, owner] using fineCarrier
      have coarseData : inFrame depth x = true ∧
          onFrameBoundary depth x = false := by
        refine ⟨?_, onFrameBoundary_eq_false_of_liftCoordinate
          (depthAt_pos owner) xPositive xMod fineData.2⟩
        simpa [inFrame_succ_liftCoordinate depth xPositive] using fineData.1
      simpa [isHorizontalCarrier, owner] using coarseData

theorem verticalCarrier_of_liftCoordinate
    {level x y : Nat} (levelPositive : 0 < level)
    (xPositive : 0 < x) (yPositive : 0 < y)
    (xMod : x % 4 = 1) (yMod : y % 4 = 1)
    (fineCarrier : isVerticalCarrier (level + 1)
      (liftCoordinate x) (liftCoordinate y) = true) :
    isVerticalCarrier level x y = true := by
  simpa only [isVerticalCarrier, isHorizontalCarrier] using
    horizontalCarrier_of_liftCoordinate levelPositive yPositive xPositive
      yMod xMod fineCarrier

theorem depthAt_eq_one_of_center_one
    {bound coordinate : Nat} (boundPositive : 0 < bound)
    (center : coordinate % period 1 = 2 * scale 1 + 1) :
    depthAt bound coordinate = some 1 := by
  have inside : inFrame 1 coordinate = true := by
    simp [inFrame, center, frameStartResidue, frameEndResidue, scale]
  have atOne : depthAt 1 coordinate = some 1 := by
    simp [depthAt, inside]
  exact depthAt_eq_some_mono atOne boundPositive

theorem center_one_not_boundary
    {coordinate : Nat}
    (center : coordinate % period 1 = 2 * scale 1 + 1) :
    onFrameBoundary 1 coordinate = false := by
  simp [onFrameBoundary, center, frameStartResidue, frameEndResidue, scale]

theorem supertileIndexGrid_succ (level x y : Nat) :
    supertileIndexGrid (level + 1) seedNode x y =
      fineGrid (supertileIndexGrid level seedNode (x / 4) (y / 4))
        (x % 4) (y % 4) := by
  change ((supertileNodeGrid level seedNode (x / 4) (y / 4)).child
      (childPosition x y)).data.parent = _
  rw [Node.child_parent, childPosition_mod_four, childPosition_div_four]
  rfl

/-- Every all-clear index-zero crossing in a canonical seed supertile is the
center of one of its recursive carrier frames. -/
theorem indexZero_crossing_centered :
    ∀ level x y : Nat,
      x < 4 ^ level →
      y < 4 ^ level →
      supertileIndexGrid level seedNode x y = 0 →
      isHorizontalCarrier level (2 * x + 1) (2 * y + 1) = true →
      isVerticalCarrier level (2 * x + 1) (2 * y + 1) = true →
      ∃ depth,
        depthAt (level - 1) (2 * y + 1) = some depth ∧
        depthAt (level - 1) (2 * x + 1) = some depth ∧
        (2 * x + 1) % period depth = 2 * scale depth + 1 ∧
        (2 * y + 1) % period depth = 2 * scale depth + 1 := by
  intro level
  induction level with
  | zero =>
      intro x y xBound yBound indexZero horizontal vertical
      simp [isHorizontalCarrier] at horizontal
  | succ level inductionHypothesis =>
      intro x y xBound yBound indexZero horizontal vertical
      have parentXBound : x / 4 < 4 ^ level := by
        rw [pow_succ] at xBound
        omega
      have parentYBound : y / 4 < 4 ^ level := by
        rw [pow_succ] at yBound
        omega
      have xDecomposition : x = 4 * (x / 4) + x % 4 := by
        have := Nat.mod_add_div x 4
        omega
      have yDecomposition : y = 4 * (y / 4) + y % 4 := by
        have := Nat.mod_add_div y 4
        omega
      have fineZero :
          fineGrid (supertileIndexGrid level seedNode (x / 4) (y / 4))
              (x % 4) (y % 4) = 0 := by
        rw [← supertileIndexGrid_succ]
        exact indexZero
      have zeroCases :=
        (fineGrid_eq_zero_iff
          (supertileIndexGrid level seedNode (x / 4) (y / 4))
          ⟨x % 4, Nat.mod_lt _ (by decide)⟩
          ⟨y % 4, Nat.mod_lt _ (by decide)⟩).1 fineZero
      rcases zeroCases with
          ⟨xLocal, yLocal, parentZero | parentFour⟩ |
          ⟨xLocal, yLocal, parentThin⟩
      · have xMod : x % 4 = 0 := by simpa using congrArg Fin.val xLocal
        have yMod : y % 4 = 0 := by simpa using congrArg Fin.val yLocal
        have parentEven := even_coordinates_of_index_zero
          parentXBound parentYBound parentZero
        let coarseX := 2 * (x / 4) + 1
        let coarseY := 2 * (y / 4) + 1
        have coarseXPositive : 0 < coarseX := by simp [coarseX]
        have coarseYPositive : 0 < coarseY := by simp [coarseY]
        have coarseXMod : coarseX % 4 = 1 := by
          simp only [coarseX]
          omega
        have coarseYMod : coarseY % 4 = 1 := by
          simp only [coarseY]
          omega
        have fineXEq : 2 * x + 1 = liftCoordinate coarseX := by
          simp only [coarseX, liftCoordinate]
          omega
        have fineYEq : 2 * y + 1 = liftCoordinate coarseY := by
          simp only [coarseY, liftCoordinate]
          omega
        have levelPositive : 0 < level := by
          by_contra notPositive
          have levelZero : level = 0 := by omega
          subst level
          simp [isHorizontalCarrier] at horizontal
        have coarseHorizontal :
            isHorizontalCarrier level coarseX coarseY = true := by
          apply horizontalCarrier_of_liftCoordinate levelPositive
            coarseXPositive coarseYPositive coarseXMod coarseYMod
          simpa only [fineXEq, fineYEq] using horizontal
        have coarseVertical :
            isVerticalCarrier level coarseX coarseY = true := by
          apply verticalCarrier_of_liftCoordinate levelPositive
            coarseXPositive coarseYPositive coarseXMod coarseYMod
          simpa only [fineXEq, fineYEq] using vertical
        rcases inductionHypothesis (x / 4) (y / 4)
            parentXBound parentYBound parentZero
            coarseHorizontal coarseVertical with
          ⟨depth, rowOwner, columnOwner, xCenter, yCenter⟩
        have rowOwnerFine :
            depthAt level (liftCoordinate coarseY) = some (depth + 1) := by
          have shifted := depthAt_liftCoordinate (level - 1) coarseY
            coarseYPositive coarseYMod
          rw [Nat.sub_add_cancel levelPositive, rowOwner] at shifted
          simpa using shifted
        have columnOwnerFine :
            depthAt level (liftCoordinate coarseX) = some (depth + 1) := by
          have shifted := depthAt_liftCoordinate (level - 1) coarseX
            coarseXPositive coarseXMod
          rw [Nat.sub_add_cancel levelPositive, columnOwner] at shifted
          simpa using shifted
        refine ⟨depth + 1, ?_, ?_, ?_, ?_⟩
        · simpa [fineYEq] using rowOwnerFine
        · simpa [fineXEq] using columnOwnerFine
        · simpa only [fineXEq] using
            liftCoordinate_centerResidue coarseXPositive xCenter
        · simpa only [fineYEq] using
            liftCoordinate_centerResidue coarseYPositive yCenter
      · have xMod : x % 4 = 0 := by simpa using congrArg Fin.val xLocal
        have yMod : y % 4 = 0 := by simpa using congrArg Fin.val yLocal
        have parentOdd := odd_coordinates_of_index_four
          parentXBound parentYBound parentFour
        let coarseX := 2 * (x / 4) + 1
        let coarseY := 2 * (y / 4) + 1
        have fineXEq : 2 * x + 1 = liftCoordinate coarseX := by
          simp only [coarseX, liftCoordinate]
          omega
        have fineYEq : 2 * y + 1 = liftCoordinate coarseY := by
          simp only [coarseY, liftCoordinate]
          omega
        have levelPositive : 0 < level := by
          by_contra notPositive
          have levelZero : level = 0 := by omega
          subst level
          simp at parentXBound
          omega
        have xCenter :
            liftCoordinate coarseX % period 1 = 2 * scale 1 + 1 := by
          simp only [coarseX, liftCoordinate, period, scale]
          omega
        have yCenter :
            liftCoordinate coarseY % period 1 = 2 * scale 1 + 1 := by
          simp only [coarseY, liftCoordinate, period, scale]
          omega
        have rowOwner : depthAt level (liftCoordinate coarseY) = some 1 :=
          depthAt_eq_one_of_center_one levelPositive yCenter
        have columnOwner : depthAt level (liftCoordinate coarseX) = some 1 :=
          depthAt_eq_one_of_center_one levelPositive xCenter
        refine ⟨1, ?_, ?_, ?_, ?_⟩
        · simpa [fineYEq] using rowOwner
        · simpa [fineXEq] using columnOwner
        · simpa only [fineXEq] using xCenter
        · simpa only [fineYEq] using yCenter
      · have xMod : x % 4 = 2 := by simpa using congrArg Fin.val xLocal
        have yMod : y % 4 = 2 := by simpa using congrArg Fin.val yLocal
        have parentPhase := supertileIndexGrid_thinPhase level
          (x / 4) (y / 4) parentXBound parentYBound
        have parentThinPhase : thinPhase (x / 4) (y / 4) = .a :=
          parentPhase.symm.trans parentThin
        have parentEven :=
          (thinPhase_eq_a_iff (x / 4) (y / 4)).1 parentThinPhase
        have levelPositive : 0 < level := by
          by_contra notPositive
          have levelZero : level = 0 := by omega
          subst level
          simp [isHorizontalCarrier] at horizontal
        have xOpening :
            (2 * x + 1) % period 1 = frameStartResidue 1 := by
          simp only [period, frameStartResidue, scale]
          omega
        have yInside : inFrame 1 (2 * y + 1) = true := by
          simp [inFrame, period, frameStartResidue, frameEndResidue, scale]
          omega
        have rowOwnerOne : depthAt 1 (2 * y + 1) = some 1 := by
          simp [depthAt, yInside]
        have rowOwner : depthAt level (2 * y + 1) = some 1 :=
          depthAt_eq_some_mono rowOwnerOne levelPositive
        have xBoundary : onFrameBoundary 1 (2 * x + 1) = true := by
          simp [onFrameBoundary, xOpening]
        simp [isHorizontalCarrier, rowOwner, xBoundary] at horizontal

/-- The distinguished marker quarter of every concrete seed supertile has
logical address zero in the recursive carrier hierarchy. -/
theorem corner_point_zero
    (level : Nat) (i j : Fin (side level))
    (corner : ShadedSignals.routedScaffold.role
      (tileRectangle level seedNode i j) = .corner) :
    point level i.val j.val = (0, 0) := by
  have roleEq :=
    eraseCorner_role_tileRectangle_seed_eq_carrierRole level i j
  have horizontal : isHorizontalCarrier level i.val j.val = true := by
    have carriers := congrArg RouteRole.isHorizontalCarrier roleEq
    rw [eraseCorner_isHorizontalCarrier,
      carrierRole_isHorizontalCarrier] at carriers
    simpa [corner, RouteRole.isHorizontalCarrier] using carriers.symm
  have vertical : isVerticalCarrier level i.val j.val = true := by
    have carriers := congrArg RouteRole.isVerticalCarrier roleEq
    rw [eraseCorner_isVerticalCarrier,
      carrierRole_isVerticalCarrier] at carriers
    simpa [corner, RouteRole.isVerticalCarrier] using carriers.symm
  have siteCorner := corner
  rw [routedRole_tileRectangle] at siteCorner
  have marker :=
    (ShadedSignals.routeRole_tile_eq_corner_iff
      (site level seedNode i.val j.val)).1 siteCorner
  have markerEq :
      (supertileIndexGrid level seedNode (i.val / 2) (j.val / 2),
          quadrantAt i.val j.val) = (0, .northeast) := by
    simpa [site, ShadedSignals.markerQuarters] using marker.2
  have indexZero :
      supertileIndexGrid level seedNode (i.val / 2) (j.val / 2) = 0 :=
    congrArg Prod.fst markerEq
  have northeast : quadrantAt i.val j.val = .northeast :=
    congrArg Prod.snd markerEq
  have parity := (quadrantAt_eq_northeast_iff i.val j.val).1 northeast
  have iEq : i.val = 2 * (i.val / 2) + 1 := by
    have decomposition := Nat.mod_add_div i.val 2
    omega
  have jEq : j.val = 2 * (j.val / 2) + 1 := by
    have decomposition := Nat.mod_add_div j.val 2
    omega
  have tileXBound : i.val / 2 < 4 ^ level := by
    have := i.isLt
    simp only [side] at this
    omega
  have tileYBound : j.val / 2 < 4 ^ level := by
    have := j.isLt
    simp only [side] at this
    omega
  have centered := indexZero_crossing_centered level
    (i.val / 2) (j.val / 2) tileXBound tileYBound indexZero
    (by simpa only [← iEq, ← jEq] using horizontal)
    (by simpa only [← iEq, ← jEq] using vertical)
  rcases centered with
    ⟨depth, rowOwner, columnOwner, xCenter, yCenter⟩
  apply point_eq_zero_of_centerResidues
    (depth := depth)
  · simpa only [← jEq] using rowOwner
  · simpa only [← iEq] using columnOwner
  · simpa only [← iEq] using xCenter
  · simpa only [← jEq] using yCenter

/-- Canonical seed supertiles, equipped with their recursive integer carrier
addresses. -/
def seedSquareAddressing (level : Nat) :
    RoutedPointedCarrierAddressing.SquareAddressing
      ShadedSignals.routedScaffold (side level) :=
  squareAddressingOfHierarchy
    (tileRectangle level seedNode)
    (validRoutedTileRectangle level seedNode)
    (eraseCorner_role_tileRectangle_seed_eq_carrierRole level)
    (corner_point_zero level)

/-- The concrete 104-tile routed scaffold realizes every pointed payload
plane. -/
theorem realizesRoutedPointedPlanes :
    RealizesRoutedPointedPlanes ShadedSignals.routedScaffold := by
  apply
    RoutedPointedCarrierAddressing.realizesRoutedPointedPlanes_of_cofinalAddressings
  intro n
  exact ⟨side n, level_le_side n, ⟨seedSquareAddressing n⟩⟩

end ShadedCarrierCornerAddressing
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
