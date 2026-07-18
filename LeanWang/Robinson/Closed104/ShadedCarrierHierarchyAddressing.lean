/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierHierarchy
import LeanWang.Robinson.Scaffold.Routed.PointedCarrierAddressing

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

private inductive AddressAxis where
  | horizontal
  | vertical

private def orientedNat : AddressAxis → Nat → Nat → Nat × Nat
  | .horizontal, along, transverse => (along, transverse)
  | .vertical, along, transverse => (transverse, along)

private def orientedInt : AddressAxis → Int → Int → Int × Int
  | .horizontal, along, transverse => (along, transverse)
  | .vertical, along, transverse => (transverse, along)

private def primaryCarrier (axis : AddressAxis) (level along transverse : Nat) : Bool :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => isHorizontalCarrier level p.1 p.2
  | .vertical => isVerticalCarrier level p.1 p.2

private def crossingCarrier (axis : AddressAxis) (level along transverse : Nat) : Bool :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => isVerticalCarrier level p.1 p.2
  | .vertical => isHorizontalCarrier level p.1 p.2

private def pointAt (axis : AddressAxis) (level along transverse : Nat) : Int × Int :=
  let p := orientedNat axis along transverse
  point level p.1 p.2

private def sourceAt (axis : AddressAxis) (level along transverse : Nat) : Int × Int :=
  let p := orientedNat axis along transverse
  match axis with
  | .horizontal => horizontalSource level p.1 p.2
  | .vertical => verticalSource level p.1 p.2

private def roleAt (axis : AddressAxis) (level along transverse : Nat) : RouteRole :=
  let p := orientedNat axis along transverse
  carrierRole level p.1 p.2

private def primaryRole : AddressAxis → RouteRole
  | .horizontal => .horizontal
  | .vertical => .vertical

private def roleIsPrimaryCarrier : AddressAxis → RouteRole → Bool
  | .horizontal => RouteRole.isHorizontalCarrier
  | .vertical => RouteRole.isVerticalCarrier

@[simp] private theorem roleAt_isPrimaryCarrier (axis : AddressAxis)
    (level along transverse : Nat) :
    roleIsPrimaryCarrier axis (roleAt axis level along transverse) =
      primaryCarrier axis level along transverse := by
  cases axis <;>
    simp [roleIsPrimaryCarrier, roleAt, primaryCarrier, orientedNat]

@[simp] private theorem eraseCorner_isPrimaryCarrier
    (axis : AddressAxis) (role : RouteRole) :
    roleIsPrimaryCarrier axis (eraseCorner role) =
      roleIsPrimaryCarrier axis role := by
  cases axis <;> cases role <;> rfl

@[simp] theorem eraseCorner_isHorizontalCarrier (role : RouteRole) :
    (eraseCorner role).isHorizontalCarrier = role.isHorizontalCarrier := by
  cases role <;> rfl

@[simp] theorem eraseCorner_isVerticalCarrier (role : RouteRole) :
    (eraseCorner role).isVerticalCarrier = role.isVerticalCarrier := by
  cases role <;> rfl

private theorem primaryCarrier_iff_of_owner
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth) :
    primaryCarrier axis level along transverse = true ↔
      inFrame depth along = true ∧ onFrameBoundary depth along = false := by
  cases axis <;>
    simp [primaryCarrier, orientedNat, isHorizontalCarrier,
      isVerticalCarrier, owner]

private theorem crossingCarrier_iff_of_owner
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) along = some depth) :
    crossingCarrier axis level along transverse = true ↔
      inFrame depth transverse = true ∧
        onFrameBoundary depth transverse = false := by
  cases axis <;>
    simp [crossingCarrier, orientedNat, isHorizontalCarrier,
      isVerticalCarrier, owner]

private theorem alongOwner_eq_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    depthAt (level - 1) along = some depth := by
  have alongInFrame := (primaryCarrier_iff_of_owner axis owner).1 primary
  cases alongOwner : depthAt (level - 1) along with
  | none =>
      cases axis <;>
        simp [crossingCarrier, orientedNat, isHorizontalCarrier,
          isVerticalCarrier, alongOwner] at crossing
  | some alongDepth =>
      have transverseInFrame :=
        (crossingCarrier_iff_of_owner axis alongOwner).1 crossing
      have sameDepth := ownerDepth_eq_of_mutual_containment
        alongOwner owner alongInFrame.1 transverseInFrame.1
      simpa [sameDepth] using alongOwner

private theorem free_eq_true_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    isFreeCoordinate depth along = true := by
  have alongData := (primaryCarrier_iff_of_owner axis owner).1 primary
  exact isFreeCoordinate_eq_true_of_owner
    (alongOwner_eq_of_mutual_carriers axis owner primary crossing)
    alongData.2

private theorem free_eq_false_of_not_crossing
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseInterior : onFrameBoundary depth transverse = false)
    (crossing : crossingCarrier axis level along transverse = false) :
    isFreeCoordinate depth along = false := by
  cases free : isFreeCoordinate depth along with
  | false => rfl
  | true =>
      have alongOwner := depthAt_eq_some_mono
        (depthAt_self_eq_some_of_isFreeCoordinate free)
        (depthAt_le owner)
      have transverseInside := inFrame_eq_true_of_depthAt_eq_some owner
      have : crossingCarrier axis level along transverse = true :=
        (crossingCarrier_iff_of_owner axis alongOwner).2
          ⟨transverseInside, transverseInterior⟩
      simp [this] at crossing

private theorem pointAt_eq_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    pointAt axis level along transverse =
      orientedInt axis (axisCoordinate depth along)
        (axisCoordinate depth transverse) := by
  have alongOwner := alongOwner_eq_of_mutual_carriers
    axis owner primary crossing
  cases axis <;>
    simp [pointAt, orientedNat, orientedInt, point, owner, alongOwner]

private theorem transverseInterior_of_mutual_carriers
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (primary : primaryCarrier axis level along transverse = true)
    (crossing : crossingCarrier axis level along transverse = true) :
    onFrameBoundary depth transverse = false := by
  have alongOwner := alongOwner_eq_of_mutual_carriers
    axis owner primary crossing
  exact ((crossingCarrier_iff_of_owner axis alongOwner).1 crossing).2

private theorem sourceAt_eq_of_transverseInterior
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseInterior : onFrameBoundary depth transverse = false) :
    sourceAt axis level along transverse =
      orientedInt axis (axisSource depth along)
        (axisCoordinate depth transverse) := by
  cases axis <;>
    simp [sourceAt, orientedNat, orientedInt, horizontalSource,
      verticalSource, owner, transverseInterior]

private theorem sourceAt_eq_zero_of_transverseBoundary
    (axis : AddressAxis) {level along transverse depth : Nat}
    (owner : depthAt (level - 1) transverse = some depth)
    (transverseBoundary : onFrameBoundary depth transverse = true) :
    sourceAt axis level along transverse = (0, 0) := by
  cases axis <;>
    simp [sourceAt, orientedNat, horizontalSource, verticalSource,
      owner, transverseBoundary]

private theorem roleAt_eq_of_primary
    (axis : AddressAxis) {level along transverse : Nat}
    (primary : primaryCarrier axis level along transverse = true) :
    roleAt axis level along transverse =
      if crossingCarrier axis level along transverse = true then .active
      else primaryRole axis := by
  cases axis with
  | horizontal =>
      change isHorizontalCarrier level along transverse = true at primary
      cases crossing : isVerticalCarrier level along transverse <;>
        simp [roleAt, crossingCarrier, primaryRole, orientedNat,
          carrierRole, primary, crossing]
  | vertical =>
      change isVerticalCarrier level transverse along = true at primary
      cases crossing : isHorizontalCarrier level transverse along <;>
        simp [roleAt, crossingCarrier, primaryRole, orientedNat,
          carrierRole, primary, crossing]

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

private def axisSuccessor : AddressAxis → Int × Int → Int × Int
  | .horizontal => horizontalSuccessor
  | .vertical => verticalSuccessor

private def axisOutgoing : AddressAxis → RouteRole →
    Int × Int → Int × Int → Int × Int
  | .horizontal => horizontalOutgoing
  | .vertical => verticalOutgoing

private def AxisStepAt (axis : AddressAxis) (level along transverse : Nat)
    (firstRole secondRole : RouteRole) : Prop :=
  let outgoing := axisOutgoing axis firstRole
    (pointAt axis level along transverse)
    (sourceAt axis level along transverse)
  match secondRole with
  | .active | .corner =>
      pointAt axis level (along + 1) transverse = axisSuccessor axis outgoing
  | .horizontal =>
      match axis with
      | .horizontal => sourceAt axis level (along + 1) transverse = outgoing
      | .vertical => False
  | .vertical =>
      match axis with
      | .horizontal => False
      | .vertical => sourceAt axis level (along + 1) transverse = outgoing
  | .inactive => False

@[simp] private theorem axisOutgoing_active (axis : AddressAxis)
    (point source : Int × Int) :
    axisOutgoing axis .active point source = point := by
  cases axis <;> rfl

@[simp] private theorem axisOutgoing_primary (axis : AddressAxis)
    (point source : Int × Int) :
    axisOutgoing axis (primaryRole axis) point source = source := by
  cases axis <;> rfl

@[simp] private theorem axisStepAt_active (axis : AddressAxis)
    (level along transverse : Nat) (firstRole : RouteRole) :
    AxisStepAt axis level along transverse firstRole .active ↔
      pointAt axis level (along + 1) transverse =
        axisSuccessor axis
          (axisOutgoing axis firstRole
            (pointAt axis level along transverse)
            (sourceAt axis level along transverse)) := by
  cases axis <;> rfl

@[simp] private theorem axisStepAt_primary (axis : AddressAxis)
    (level along transverse : Nat) (firstRole : RouteRole) :
    AxisStepAt axis level along transverse firstRole (primaryRole axis) ↔
      sourceAt axis level (along + 1) transverse =
        axisOutgoing axis firstRole
          (pointAt axis level along transverse)
          (sourceAt axis level along transverse) := by
  cases axis <;> rfl

@[simp] private theorem axisSuccessor_oriented (axis : AddressAxis)
    (along transverse : Int) :
    axisSuccessor axis (orientedInt axis along transverse) =
      orientedInt axis (along + 1) transverse := by
  cases axis <;> rfl

private theorem axis_step (axis : AddressAxis) (level along transverse : Nat)
    (firstPrimary : primaryCarrier axis level along transverse = true)
    (secondPrimary :
      primaryCarrier axis level (along + 1) transverse = true) :
    AxisStepAt axis level along transverse
      (roleAt axis level along transverse)
      (roleAt axis level (along + 1) transverse) := by
  cases owner : depthAt (level - 1) transverse with
  | none =>
      cases axis <;>
        simp [primaryCarrier, orientedNat, isHorizontalCarrier,
          isVerticalCarrier, owner] at firstPrimary
  | some depth =>
      have firstData :=
        (primaryCarrier_iff_of_owner axis owner).1 firstPrimary
      have secondData :=
        (primaryCarrier_iff_of_owner axis owner).1 secondPrimary
      have sameCenter := frameCenter_succ_of_inFrame_not_boundary
        firstData.1 firstData.2
      cases transverseBoundary : onFrameBoundary depth transverse with
      | true =>
          have firstCrossing :
              crossingCarrier axis level along transverse = false := by
            cases crossing : crossingCarrier axis level along transverse with
            | false => rfl
            | true =>
                have interior := transverseInterior_of_mutual_carriers
                  axis owner firstPrimary crossing
                simp [transverseBoundary] at interior
          have secondCrossing : crossingCarrier axis level (along + 1)
              transverse = false := by
            cases crossing : crossingCarrier axis level (along + 1) transverse with
            | false => rfl
            | true =>
                have interior := transverseInterior_of_mutual_carriers
                  axis owner secondPrimary crossing
                simp [transverseBoundary] at interior
          have firstRole := roleAt_eq_of_primary axis firstPrimary
          have secondRole := roleAt_eq_of_primary axis secondPrimary
          simp [firstCrossing] at firstRole
          simp [secondCrossing] at secondRole
          rw [firstRole, secondRole, axisStepAt_primary,
            axisOutgoing_primary,
            sourceAt_eq_zero_of_transverseBoundary axis owner
              transverseBoundary,
            sourceAt_eq_zero_of_transverseBoundary axis owner
              transverseBoundary]
      | false =>
          cases firstCrossing : crossingCarrier axis level along transverse with
          | false =>
              have firstFree := free_eq_false_of_not_crossing
                axis owner transverseBoundary firstCrossing
              have firstSource := sourceAt_eq_of_transverseInterior
                (along := along) axis owner transverseBoundary
              have firstRole := roleAt_eq_of_primary axis firstPrimary
              simp [firstCrossing] at firstRole
              cases secondCrossing :
                  crossingCarrier axis level (along + 1) transverse with
              | false =>
                  have secondSource := sourceAt_eq_of_transverseInterior
                    (along := along + 1) axis owner transverseBoundary
                  have secondRole := roleAt_eq_of_primary axis secondPrimary
                  simp [secondCrossing] at secondRole
                  rw [firstRole, secondRole, axisStepAt_primary,
                    axisOutgoing_primary, firstSource, secondSource,
                    axisSource_succ_of_not_free firstFree sameCenter]
              | true =>
                  have secondPoint := pointAt_eq_of_mutual_carriers
                    axis owner secondPrimary secondCrossing
                  have secondRole := roleAt_eq_of_primary axis secondPrimary
                  simp [secondCrossing] at secondRole
                  rw [firstRole, secondRole, axisStepAt_active,
                    axisOutgoing_primary, firstSource, secondPoint,
                    axisSuccessor_oriented,
                    axisCoordinate_succ_of_not_free firstFree sameCenter]
          | true =>
              have firstFree := free_eq_true_of_mutual_carriers
                axis owner firstPrimary firstCrossing
              have firstPoint := pointAt_eq_of_mutual_carriers
                axis owner firstPrimary firstCrossing
              have firstRole := roleAt_eq_of_primary axis firstPrimary
              simp [firstCrossing] at firstRole
              cases secondCrossing :
                  crossingCarrier axis level (along + 1) transverse with
              | false =>
                  have secondSource := sourceAt_eq_of_transverseInterior
                    (along := along + 1) axis owner transverseBoundary
                  have secondRole := roleAt_eq_of_primary axis secondPrimary
                  simp [secondCrossing] at secondRole
                  rw [firstRole, secondRole, axisStepAt_primary,
                    axisOutgoing_active, firstPoint, secondSource,
                    axisSource_succ_of_free firstFree sameCenter]
              | true =>
                  have secondPoint := pointAt_eq_of_mutual_carriers
                    axis owner secondPrimary secondCrossing
                  have secondRole := roleAt_eq_of_primary axis secondPrimary
                  simp [secondCrossing] at secondRole
                  rw [firstRole, secondRole, axisStepAt_active,
                    axisOutgoing_active, firstPoint, secondPoint,
                    axisSuccessor_oriented,
                    axisCoordinate_succ_of_free firstFree sameCenter]

def HorizontalStepAt (level x y : Nat) (leftRole rightRole : RouteRole) : Prop :=
  AxisStepAt .horizontal level x y leftRole rightRole

def VerticalStepAt (level x y : Nat) (lowerRole upperRole : RouteRole) : Prop :=
  AxisStepAt .vertical level y x lowerRole upperRole

/-- Replacing an active hierarchy role by the corner marker preserves the
axis-neutral addressing step. -/
private theorem axis_step_of_erased_roles
    (axis : AddressAxis) (level along transverse : Nat)
    (firstRole secondRole : RouteRole)
    (firstRoleEq : eraseCorner firstRole = roleAt axis level along transverse)
    (secondRoleEq : eraseCorner secondRole =
      roleAt axis level (along + 1) transverse)
    (firstCarrier : roleIsPrimaryCarrier axis firstRole = true)
    (secondCarrier : roleIsPrimaryCarrier axis secondRole = true) :
    AxisStepAt axis level along transverse firstRole secondRole := by
  have firstPrimary : primaryCarrier axis level along transverse = true := by
    rw [← roleAt_isPrimaryCarrier, ← firstRoleEq,
      eraseCorner_isPrimaryCarrier]
    exact firstCarrier
  have secondPrimary :
      primaryCarrier axis level (along + 1) transverse = true := by
    rw [← roleAt_isPrimaryCarrier, ← secondRoleEq,
      eraseCorner_isPrimaryCarrier]
    exact secondCarrier
  have step := axis_step axis level along transverse firstPrimary secondPrimary
  rw [← firstRoleEq, ← secondRoleEq] at step
  cases axis <;> cases firstRole <;> cases secondRole <;>
    simp only [roleIsPrimaryCarrier, RouteRole.isHorizontalCarrier,
      RouteRole.isVerticalCarrier] at firstCarrier secondCarrier <;>
    simp only [eraseCorner, AxisStepAt, axisOutgoing, pointAt, sourceAt,
      orientedNat, axisSuccessor] at step ⊢ <;>
    exact step

/-- Replace the hierarchy's erased active role by either an ordinary active
crossing or the distinguished corner marker. -/
theorem horizontal_step_of_erased_roles
    (level x y : Nat) (leftRole rightRole : RouteRole)
    (leftRoleEq : eraseCorner leftRole = carrierRole level x y)
    (rightRoleEq : eraseCorner rightRole = carrierRole level (x + 1) y)
    (leftCarrier : leftRole.isHorizontalCarrier = true)
    (rightCarrier : rightRole.isHorizontalCarrier = true) :
    HorizontalStepAt level x y leftRole rightRole := by
  unfold HorizontalStepAt
  exact axis_step_of_erased_roles .horizontal level x y leftRole rightRole
    leftRoleEq rightRoleEq leftCarrier rightCarrier

/-- Vertical counterpart of `horizontal_step_of_erased_roles`. -/
theorem vertical_step_of_erased_roles
    (level x y : Nat) (lowerRole upperRole : RouteRole)
    (lowerRoleEq : eraseCorner lowerRole = carrierRole level x y)
    (upperRoleEq : eraseCorner upperRole = carrierRole level x (y + 1))
    (lowerCarrier : lowerRole.isVerticalCarrier = true)
    (upperCarrier : upperRole.isVerticalCarrier = true) :
    VerticalStepAt level x y lowerRole upperRole := by
  unfold VerticalStepAt
  exact axis_step_of_erased_roles .vertical level y x lowerRole upperRole
    lowerRoleEq upperRoleEq lowerCarrier upperCarrier

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
      simpa only [HorizontalStepAt, AxisStepAt, axisOutgoing, pointAt,
        sourceAt, orientedNat, axisSuccessor, rightRole, Fin.val_mk] using step
  vstep := by
    intro i j hj lowerCarrier upperCarrier
    have step := vertical_step_of_erased_roles level i.val j.val
      (S.role (base i j))
      (S.role (base i ⟨j.val + 1, hj⟩))
      (roleEq i j) (roleEq i ⟨j.val + 1, hj⟩)
      lowerCarrier upperCarrier
    cases upperRole : S.role (base i ⟨j.val + 1, hj⟩) <;>
      simp only [upperRole, RouteRole.isVerticalCarrier] at upperCarrier <;>
      simpa only [VerticalStepAt, AxisStepAt, axisOutgoing, pointAt,
        sourceAt, orientedNat, axisSuccessor, upperRole, Fin.val_mk] using step

end ShadedCarrierHierarchyAddressing
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
