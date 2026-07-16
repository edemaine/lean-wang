/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.OllingerRobinson104ShadedCarrierHierarchy
import LeanWang.RoutedPointedCarrierAddressing

/-!
# Logical addresses on the shaded carrier hierarchy

The smallest enclosing Robinson frame determines both carrier connectivity and
logical coordinates.  Free coordinates count the active grid vertices; an
entire nested frame is therefore one channel gap.  This file proves the local
successor equations independently of the concrete 104-tile substitution.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierHierarchyAddressing

open RoutedPointedCarrierAddressing
open ShadedCarrierHierarchy

/-- Logical crossing address predicted by the row and column owner frames. -/
def point (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) y, depthAt (level - 1) x with
  | some rowDepth, some columnDepth =>
      (axisCoordinate rowDepth x, axisCoordinate columnDepth y)
  | _, _ => (0, 0)

/-- Address held constant along a horizontal channel gap.  Boundary rows have
no crossings, so they may carry the arbitrary zero address. -/
def horizontalSource (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) y with
  | none => (0, 0)
  | some depth =>
      if onFrameBoundary depth y then (0, 0)
      else (axisSource depth x, axisCoordinate depth y)

/-- Address held constant along a vertical channel gap. -/
def verticalSource (level x y : Nat) : Int × Int :=
  match depthAt (level - 1) x with
  | none => (0, 0)
  | some depth =>
      if onFrameBoundary depth x then (0, 0)
      else (axisCoordinate depth x, axisSource depth y)

theorem horizontalCarrier_iff_of_rowOwner
    {level x y depth : Nat}
    (owner : depthAt (level - 1) y = some depth) :
    isHorizontalCarrier level x y = true ↔
      inFrame depth x = true ∧ onFrameBoundary depth x = false := by
  simp [isHorizontalCarrier, owner]

theorem verticalCarrier_iff_of_columnOwner
    {level x y depth : Nat}
    (owner : depthAt (level - 1) x = some depth) :
    isVerticalCarrier level x y = true ↔
      inFrame depth y = true ∧ onFrameBoundary depth y = false := by
  simp [isVerticalCarrier, owner]

/-- A mutual crossing forces the column to have the row's owner depth. -/
theorem columnOwner_eq_rowOwner_of_mutual_carriers
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    depthAt (level - 1) x = some depth := by
  have xInRow := (horizontalCarrier_iff_of_rowOwner rowOwner).1 horizontal
  cases columnOwner : depthAt (level - 1) x with
  | none => simp [isVerticalCarrier, columnOwner] at vertical
  | some columnDepth =>
      have yInColumn :=
        (verticalCarrier_iff_of_columnOwner columnOwner).1 vertical
      have sameDepth := ownerDepth_eq_of_mutual_containment
        columnOwner rowOwner xInRow.1 yInColumn.1
      simpa [sameDepth] using columnOwner

theorem free_eq_true_of_mutual_carriers
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    isFreeCoordinate depth x = true := by
  have xData := (horizontalCarrier_iff_of_rowOwner rowOwner).1 horizontal
  exact isFreeCoordinate_eq_true_of_owner
    (columnOwner_eq_rowOwner_of_mutual_carriers rowOwner horizontal vertical)
    xData.2

theorem free_eq_false_of_horizontal_not_vertical
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (rowInterior : onFrameBoundary depth y = false)
    (vertical : isVerticalCarrier level x y = false) :
    isFreeCoordinate depth x = false := by
  cases free : isFreeCoordinate depth x with
  | false => rfl
  | true =>
      have columnOwner := depthAt_eq_some_mono
        (depthAt_self_eq_some_of_isFreeCoordinate free)
        (depthAt_le rowOwner)
      have rowInside := inFrame_eq_true_of_depthAt_eq_some rowOwner
      have : isVerticalCarrier level x y = true :=
        (verticalCarrier_iff_of_columnOwner columnOwner).2
          ⟨rowInside, rowInterior⟩
      simp [this] at vertical

theorem point_eq_of_mutual_carriers
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    point level x y =
      (axisCoordinate depth x, axisCoordinate depth y) := by
  have columnOwner := columnOwner_eq_rowOwner_of_mutual_carriers
    rowOwner horizontal vertical
  simp [point, rowOwner, columnOwner]

theorem rowInterior_of_mutual_carriers
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    onFrameBoundary depth y = false := by
  have columnOwner := columnOwner_eq_rowOwner_of_mutual_carriers
    rowOwner horizontal vertical
  exact ((verticalCarrier_iff_of_columnOwner columnOwner).1 vertical).2

theorem horizontalSource_eq_of_rowInterior
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (rowInterior : onFrameBoundary depth y = false) :
    horizontalSource level x y =
      (axisSource depth x, axisCoordinate depth y) := by
  simp [horizontalSource, rowOwner, rowInterior]

/-- A mutual crossing also forces the row to have the column's owner depth. -/
theorem rowOwner_eq_columnOwner_of_mutual_carriers
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    depthAt (level - 1) y = some depth := by
  have yInColumn := (verticalCarrier_iff_of_columnOwner columnOwner).1 vertical
  cases rowOwner : depthAt (level - 1) y with
  | none => simp [isHorizontalCarrier, rowOwner] at horizontal
  | some rowDepth =>
      have xInRow :=
        (horizontalCarrier_iff_of_rowOwner rowOwner).1 horizontal
      have sameDepth := ownerDepth_eq_of_mutual_containment
        columnOwner rowOwner xInRow.1 yInColumn.1
      simpa [sameDepth] using rowOwner

theorem free_eq_true_of_mutual_carriers_vertical
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    isFreeCoordinate depth y = true := by
  have yData := (verticalCarrier_iff_of_columnOwner columnOwner).1 vertical
  exact isFreeCoordinate_eq_true_of_owner
    (rowOwner_eq_columnOwner_of_mutual_carriers
      columnOwner horizontal vertical)
    yData.2

theorem free_eq_false_of_vertical_not_horizontal
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (columnInterior : onFrameBoundary depth x = false)
    (horizontal : isHorizontalCarrier level x y = false) :
    isFreeCoordinate depth y = false := by
  cases free : isFreeCoordinate depth y with
  | false => rfl
  | true =>
      have rowOwner := depthAt_eq_some_mono
        (depthAt_self_eq_some_of_isFreeCoordinate free)
        (depthAt_le columnOwner)
      have columnInside := inFrame_eq_true_of_depthAt_eq_some columnOwner
      have : isHorizontalCarrier level x y = true :=
        (horizontalCarrier_iff_of_rowOwner rowOwner).2
          ⟨columnInside, columnInterior⟩
      simp [this] at horizontal

theorem point_eq_of_mutual_carriers_vertical
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    point level x y =
      (axisCoordinate depth x, axisCoordinate depth y) := by
  have rowOwner := rowOwner_eq_columnOwner_of_mutual_carriers
    columnOwner horizontal vertical
  simp [point, rowOwner, columnOwner]

theorem columnInterior_of_mutual_carriers
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (horizontal : isHorizontalCarrier level x y = true)
    (vertical : isVerticalCarrier level x y = true) :
    onFrameBoundary depth x = false := by
  have rowOwner := rowOwner_eq_columnOwner_of_mutual_carriers
    columnOwner horizontal vertical
  exact ((horizontalCarrier_iff_of_rowOwner rowOwner).1 horizontal).2

theorem verticalSource_eq_of_columnInterior
    {level x y depth : Nat}
    (columnOwner : depthAt (level - 1) x = some depth)
    (columnInterior : onFrameBoundary depth x = false) :
    verticalSource level x y =
      (axisCoordinate depth x, axisSource depth y) := by
  simp [verticalSource, columnOwner, columnInterior]

theorem point_eq_zero_of_centerResidues
    {level x y depth : Nat}
    (rowOwner : depthAt (level - 1) y = some depth)
    (columnOwner : depthAt (level - 1) x = some depth)
    (xCenter : x % period depth = 2 * scale depth + 1)
    (yCenter : y % period depth = 2 * scale depth + 1) :
    point level x y = (0, 0) := by
  simp [point, rowOwner, columnOwner,
    axisCoordinate_eq_zero_of_centerResidue xCenter,
    axisCoordinate_eq_zero_of_centerResidue yCenter]

/-- Adjacent horizontal hierarchy carriers satisfy the symbolic address
equation used by `SquareAddressing`. -/
theorem horizontal_step (level x y : Nat)
    (leftCarrier :
      (carrierRole level x y).isHorizontalCarrier = true)
    (rightCarrier :
      (carrierRole level (x + 1) y).isHorizontalCarrier = true) :
    let outgoing := horizontalOutgoing (carrierRole level x y)
      (point level x y) (horizontalSource level x y)
    match carrierRole level (x + 1) y with
    | .active | .corner =>
        point level (x + 1) y = horizontalSuccessor outgoing
    | .horizontal => horizontalSource level (x + 1) y = outgoing
    | .inactive | .vertical => False := by
  have leftHorizontal : isHorizontalCarrier level x y = true := by
    simpa using leftCarrier
  have rightHorizontal : isHorizontalCarrier level (x + 1) y = true := by
    simpa using rightCarrier
  cases rowOwner : depthAt (level - 1) y with
  | none => simp [isHorizontalCarrier, rowOwner] at leftHorizontal
  | some depth =>
      have leftData :=
        (horizontalCarrier_iff_of_rowOwner rowOwner).1 leftHorizontal
      have rightData :=
        (horizontalCarrier_iff_of_rowOwner rowOwner).1 rightHorizontal
      have sameCenter := frameCenter_succ_of_inFrame_not_boundary
        leftData.1 leftData.2
      cases rowBoundary : onFrameBoundary depth y with
      | true =>
          have leftVertical : isVerticalCarrier level x y = false := by
            cases vertical : isVerticalCarrier level x y with
            | false => rfl
            | true =>
                have interior := rowInterior_of_mutual_carriers
                  rowOwner leftHorizontal vertical
                simp [rowBoundary] at interior
          have rightVertical :
              isVerticalCarrier level (x + 1) y = false := by
            cases vertical : isVerticalCarrier level (x + 1) y with
            | false => rfl
            | true =>
                have interior := rowInterior_of_mutual_carriers
                  rowOwner rightHorizontal vertical
                simp [rowBoundary] at interior
          simp [carrierRole, leftHorizontal, rightHorizontal, leftVertical,
            rightVertical, horizontalSource, rowOwner, rowBoundary,
            horizontalOutgoing]
      | false =>
          cases leftVertical : isVerticalCarrier level x y with
          | false =>
              have leftFree := free_eq_false_of_horizontal_not_vertical
                rowOwner rowBoundary leftVertical
              have leftSource := horizontalSource_eq_of_rowInterior
                (x := x) rowOwner rowBoundary
              cases rightVertical : isVerticalCarrier level (x + 1) y with
              | false =>
                  have rightSource := horizontalSource_eq_of_rowInterior
                    (x := x + 1) rowOwner rowBoundary
                  simp [carrierRole, leftHorizontal, rightHorizontal,
                    leftVertical, rightVertical, horizontalOutgoing]
                  rw [leftSource, rightSource,
                    axisSource_succ_of_not_free leftFree sameCenter]
              | true =>
                  have rightPoint := point_eq_of_mutual_carriers
                    rowOwner rightHorizontal rightVertical
                  simp [carrierRole, leftHorizontal, rightHorizontal,
                    leftVertical, rightVertical, horizontalOutgoing,
                    horizontalSuccessor]
                  rw [leftSource, rightPoint,
                    axisCoordinate_succ_of_not_free leftFree sameCenter]
          | true =>
              have leftFree := free_eq_true_of_mutual_carriers
                rowOwner leftHorizontal leftVertical
              have leftPoint := point_eq_of_mutual_carriers
                rowOwner leftHorizontal leftVertical
              cases rightVertical : isVerticalCarrier level (x + 1) y with
              | false =>
                  have rightSource := horizontalSource_eq_of_rowInterior
                    (x := x + 1) rowOwner rowBoundary
                  simp [carrierRole, leftHorizontal, rightHorizontal,
                    leftVertical, rightVertical, horizontalOutgoing]
                  rw [leftPoint, rightSource,
                    axisSource_succ_of_free leftFree sameCenter]
              | true =>
                  have rightPoint := point_eq_of_mutual_carriers
                    rowOwner rightHorizontal rightVertical
                  simp [carrierRole, leftHorizontal, rightHorizontal,
                    leftVertical, rightVertical, horizontalOutgoing,
                    horizontalSuccessor]
                  rw [leftPoint, rightPoint,
                    axisCoordinate_succ_of_free leftFree sameCenter]

/-- Adjacent vertical hierarchy carriers satisfy the symbolic address equation
used by `SquareAddressing`. -/
theorem vertical_step (level x y : Nat)
    (lowerCarrier :
      (carrierRole level x y).isVerticalCarrier = true)
    (upperCarrier :
      (carrierRole level x (y + 1)).isVerticalCarrier = true) :
    let outgoing := verticalOutgoing (carrierRole level x y)
      (point level x y) (verticalSource level x y)
    match carrierRole level x (y + 1) with
    | .active | .corner =>
        point level x (y + 1) = verticalSuccessor outgoing
    | .vertical => verticalSource level x (y + 1) = outgoing
    | .inactive | .horizontal => False := by
  have lowerVertical : isVerticalCarrier level x y = true := by
    simpa using lowerCarrier
  have upperVertical : isVerticalCarrier level x (y + 1) = true := by
    simpa using upperCarrier
  cases columnOwner : depthAt (level - 1) x with
  | none => simp [isVerticalCarrier, columnOwner] at lowerVertical
  | some depth =>
      have lowerData :=
        (verticalCarrier_iff_of_columnOwner columnOwner).1 lowerVertical
      have upperData :=
        (verticalCarrier_iff_of_columnOwner columnOwner).1 upperVertical
      have sameCenter := frameCenter_succ_of_inFrame_not_boundary
        lowerData.1 lowerData.2
      cases columnBoundary : onFrameBoundary depth x with
      | true =>
          have lowerHorizontal : isHorizontalCarrier level x y = false := by
            cases horizontal : isHorizontalCarrier level x y with
            | false => rfl
            | true =>
                have interior := columnInterior_of_mutual_carriers
                  columnOwner horizontal lowerVertical
                simp [columnBoundary] at interior
          have upperHorizontal :
              isHorizontalCarrier level x (y + 1) = false := by
            cases horizontal : isHorizontalCarrier level x (y + 1) with
            | false => rfl
            | true =>
                have interior := columnInterior_of_mutual_carriers
                  columnOwner horizontal upperVertical
                simp [columnBoundary] at interior
          simp [carrierRole, lowerVertical, upperVertical, lowerHorizontal,
            upperHorizontal, verticalSource, columnOwner, columnBoundary,
            verticalOutgoing]
      | false =>
          cases lowerHorizontal : isHorizontalCarrier level x y with
          | false =>
              have lowerFree := free_eq_false_of_vertical_not_horizontal
                columnOwner columnBoundary lowerHorizontal
              have lowerSource := verticalSource_eq_of_columnInterior
                (y := y) columnOwner columnBoundary
              cases upperHorizontal : isHorizontalCarrier level x (y + 1) with
              | false =>
                  have upperSource := verticalSource_eq_of_columnInterior
                    (y := y + 1) columnOwner columnBoundary
                  simp [carrierRole, lowerVertical, upperVertical,
                    lowerHorizontal, upperHorizontal, verticalOutgoing]
                  rw [lowerSource, upperSource,
                    axisSource_succ_of_not_free lowerFree sameCenter]
              | true =>
                  have upperPoint := point_eq_of_mutual_carriers_vertical
                    columnOwner upperHorizontal upperVertical
                  simp [carrierRole, lowerVertical, upperVertical,
                    lowerHorizontal, upperHorizontal, verticalOutgoing,
                    verticalSuccessor]
                  rw [lowerSource, upperPoint,
                    axisCoordinate_succ_of_not_free lowerFree sameCenter]
          | true =>
              have lowerFree := free_eq_true_of_mutual_carriers_vertical
                columnOwner lowerHorizontal lowerVertical
              have lowerPoint := point_eq_of_mutual_carriers_vertical
                columnOwner lowerHorizontal lowerVertical
              cases upperHorizontal : isHorizontalCarrier level x (y + 1) with
              | false =>
                  have upperSource := verticalSource_eq_of_columnInterior
                    (y := y + 1) columnOwner columnBoundary
                  simp [carrierRole, lowerVertical, upperVertical,
                    lowerHorizontal, upperHorizontal, verticalOutgoing]
                  rw [lowerPoint, upperSource,
                    axisSource_succ_of_free lowerFree sameCenter]
              | true =>
                  have upperPoint := point_eq_of_mutual_carriers_vertical
                    columnOwner upperHorizontal upperVertical
                  simp [carrierRole, lowerVertical, upperVertical,
                    lowerHorizontal, upperHorizontal, verticalOutgoing,
                    verticalSuccessor]
                  rw [lowerPoint, upperPoint,
                    axisCoordinate_succ_of_free lowerFree sameCenter]

@[simp] theorem eraseCorner_isHorizontalCarrier (role : RouteRole) :
    (eraseCorner role).isHorizontalCarrier = role.isHorizontalCarrier := by
  cases role <;> rfl

@[simp] theorem eraseCorner_isVerticalCarrier (role : RouteRole) :
    (eraseCorner role).isVerticalCarrier = role.isVerticalCarrier := by
  cases role <;> rfl

def HorizontalStepAt (level x y : Nat) (leftRole rightRole : RouteRole) : Prop :=
  let outgoing := horizontalOutgoing leftRole
    (point level x y) (horizontalSource level x y)
  match rightRole with
  | .active | .corner =>
      point level (x + 1) y = horizontalSuccessor outgoing
  | .horizontal => horizontalSource level (x + 1) y = outgoing
  | .inactive | .vertical => False

def VerticalStepAt (level x y : Nat) (lowerRole upperRole : RouteRole) : Prop :=
  let outgoing := verticalOutgoing lowerRole
    (point level x y) (verticalSource level x y)
  match upperRole with
  | .active | .corner =>
      point level x (y + 1) = verticalSuccessor outgoing
  | .vertical => verticalSource level x (y + 1) = outgoing
  | .inactive | .horizontal => False

/-- Replace the hierarchy's erased active role by either an ordinary active
crossing or the distinguished corner marker. -/
theorem horizontal_step_of_erased_roles
    (level x y : Nat) (leftRole rightRole : RouteRole)
    (leftRoleEq : eraseCorner leftRole = carrierRole level x y)
    (rightRoleEq : eraseCorner rightRole = carrierRole level (x + 1) y)
    (leftCarrier : leftRole.isHorizontalCarrier = true)
    (rightCarrier : rightRole.isHorizontalCarrier = true) :
    HorizontalStepAt level x y leftRole rightRole := by
  have leftCarrier' :
      (carrierRole level x y).isHorizontalCarrier = true := by
    rw [← leftRoleEq, eraseCorner_isHorizontalCarrier]
    exact leftCarrier
  have rightCarrier' :
      (carrierRole level (x + 1) y).isHorizontalCarrier = true := by
    rw [← rightRoleEq, eraseCorner_isHorizontalCarrier]
    exact rightCarrier
  have step := horizontal_step level x y leftCarrier' rightCarrier'
  rw [← leftRoleEq, ← rightRoleEq] at step
  unfold HorizontalStepAt
  cases leftRole <;> cases rightRole <;>
    simp only [RouteRole.isHorizontalCarrier] at leftCarrier rightCarrier <;>
    simp only [eraseCorner, horizontalOutgoing] at step ⊢ <;>
    exact step

/-- Vertical counterpart of `horizontal_step_of_erased_roles`. -/
theorem vertical_step_of_erased_roles
    (level x y : Nat) (lowerRole upperRole : RouteRole)
    (lowerRoleEq : eraseCorner lowerRole = carrierRole level x y)
    (upperRoleEq : eraseCorner upperRole = carrierRole level x (y + 1))
    (lowerCarrier : lowerRole.isVerticalCarrier = true)
    (upperCarrier : upperRole.isVerticalCarrier = true) :
    VerticalStepAt level x y lowerRole upperRole := by
  have lowerCarrier' :
      (carrierRole level x y).isVerticalCarrier = true := by
    rw [← lowerRoleEq, eraseCorner_isVerticalCarrier]
    exact lowerCarrier
  have upperCarrier' :
      (carrierRole level x (y + 1)).isVerticalCarrier = true := by
    rw [← upperRoleEq, eraseCorner_isVerticalCarrier]
    exact upperCarrier
  have step := vertical_step level x y lowerCarrier' upperCarrier'
  rw [← lowerRoleEq, ← upperRoleEq] at step
  unfold VerticalStepAt
  cases lowerRole <;> cases upperRole <;>
    simp only [RouteRole.isVerticalCarrier] at lowerCarrier upperCarrier <;>
    simp only [eraseCorner, verticalOutgoing] at step ⊢ <;>
    exact step

/-- Turn a concrete square whose roles follow the hierarchy into an addressed
carrier square.  The concrete substitution proof only has to supply role
recognition and centered corner markers. -/
def squareAddressingOfHierarchy
    {S : RoutedScaffold} {n level : Nat}
    (base : Rectangle n n) (baseValid : ValidRectangle S.tiles base)
    (roleEq : ∀ i j,
      eraseCorner (S.role (base i j)) = carrierRole level i.val j.val)
    (cornerZero : ∀ i j, S.role (base i j) = .corner →
      point level i.val j.val = (0, 0)) :
    SquareAddressing S n where
  base := base
  base_valid := baseValid
  point := fun i j => point level i.val j.val
  horizontalSource := fun i j => horizontalSource level i.val j.val
  verticalSource := fun i j => verticalSource level i.val j.val
  corner_zero := cornerZero
  hstep := by
    intro i j hi leftCarrier rightCarrier
    have step := horizontal_step_of_erased_roles level i.val j.val
      (S.role (base i j))
      (S.role (base ⟨i.val + 1, hi⟩ j))
      (roleEq i j) (roleEq ⟨i.val + 1, hi⟩ j)
      leftCarrier rightCarrier
    cases rightRole : S.role (base ⟨i.val + 1, hi⟩ j) <;>
      simp only [rightRole, RouteRole.isHorizontalCarrier] at rightCarrier <;>
      simpa only [HorizontalStepAt, rightRole, Fin.val_mk] using step
  vstep := by
    intro i j hj lowerCarrier upperCarrier
    have step := vertical_step_of_erased_roles level i.val j.val
      (S.role (base i j))
      (S.role (base i ⟨j.val + 1, hj⟩))
      (roleEq i j) (roleEq i ⟨j.val + 1, hj⟩)
      lowerCarrier upperCarrier
    cases upperRole : S.role (base i ⟨j.val + 1, hj⟩) <;>
      simp only [upperRole, RouteRole.isVerticalCarrier] at upperCarrier <;>
      simpa only [VerticalStepAt, upperRole, Fin.val_mk] using step

end ShadedCarrierHierarchyAddressing
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
