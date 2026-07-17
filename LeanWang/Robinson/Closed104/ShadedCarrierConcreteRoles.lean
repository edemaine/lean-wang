/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedCarrierBorderIntervals
import LeanWang.Robinson.Closed104.ShadedCarrierSquareGeometry

/-!
# Concrete carrier roles in canonical shaded supertiles

The certified border factor identifies every bounded row and column of the
seed supertile with the recursive selected-border formula. Canonical interval
edges depend only on that bounded prefix, so their concrete clear cells are
exactly the arithmetic carrier cells.
-/

noncomputable section

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace ShadedCarrierConcreteRoles

open ShadedCarrierHierarchy
open ShadedCarrierBorderHierarchy
open ShadedCarrierBorderGeometry
open ShadedCarrierSquareGeometry
open ShadedSubstitution
open ShadedSubstitutionPlane

theorem previousInterior_congr_of_lt
    {left right : Nat → Option Bool} {position : Nat}
    (equal : ∀ coordinate, coordinate < position →
      left coordinate = right coordinate) :
    ShadedSignalRectangle.previousInterior left position =
      ShadedSignalRectangle.previousInterior right position := by
  induction position with
  | zero => rfl
  | succ position inductionHypothesis =>
      have current := equal position (by omega)
      cases rightCurrent : right position with
      | none =>
          have prior := inductionHypothesis fun coordinate lower =>
            equal coordinate (lower.trans (by omega))
          simp [ShadedSignalRectangle.previousInterior, current,
            rightCurrent, prior]
      | some orientation =>
          simp [ShadedSignalRectangle.previousInterior, current, rightCurrent]

theorem nextInterior_congr_of_lt
    {left right : Nat → Option Bool} {length position fuel : Nat}
    (bounded : position + fuel ≤ length)
    (equal : ∀ coordinate, coordinate < length →
      left coordinate = right coordinate) :
    ShadedSignalRectangle.nextInterior left position fuel =
      ShadedSignalRectangle.nextInterior right position fuel := by
  induction fuel generalizing position with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      have position_lt : position < length := by omega
      have current := equal position position_lt
      cases rightCurrent : right position with
      | none =>
          have tail := inductionHypothesis (position := position + 1)
            (by omega)
          simp [ShadedSignalRectangle.nextInterior, current,
            rightCurrent, tail]
      | some orientation =>
          simp [ShadedSignalRectangle.nextInterior, current, rightCurrent]

theorem intervalEdge_congr_of_lt
    {left right : Nat → Option Bool} {length position : Nat}
    (bounded : position ≤ length)
    (equal : ∀ coordinate, coordinate < length →
      left coordinate = right coordinate) :
    ShadedSignalRectangle.intervalEdge left length position =
      ShadedSignalRectangle.intervalEdge right length position := by
  have nextEqual := nextInterior_congr_of_lt
    (left := left) (right := right) (length := length)
    (position := position) (fuel := length - position)
    (by omega) equal
  have previousEqual := previousInterior_congr_of_lt
    (left := left) (right := right) (position := position)
    fun coordinate lower => equal coordinate (lower.trans_le bounded)
  unfold ShadedSignalRectangle.intervalEdge
  rw [nextEqual, previousEqual]

theorem horizontalEdge_seed_eq_selectedBorder_intervalEdge
    (level y position : Nat) (hy : y < side level)
    (hposition : position ≤ side level) :
    horizontalEdge level seedNode y position =
      ShadedSignalRectangle.intervalEdge
        (fun x => selectedBorder level x y) (2 * scale level) position := by
  have sideEq : side level = 2 * scale level := by
    rfl
  unfold horizontalEdge
  rw [sideEq]
  apply intervalEdge_congr_of_lt
  · simpa [sideEq] using hposition
  · intro coordinate coordinate_lt
    apply rowInterior_seed_eq_selectedBorder
    · simpa [sideEq] using coordinate_lt
    · exact hy

theorem verticalEdge_seed_eq_selectedBorder_intervalEdge
    (level x position : Nat) (hx : x < side level)
    (hposition : position ≤ side level) :
    verticalEdge level seedNode x position =
      ShadedSignalRectangle.intervalEdge
        (fun y => selectedBorder level y x) (2 * scale level) position := by
  have sideEq : side level = 2 * scale level := by
    rfl
  unfold verticalEdge
  rw [sideEq]
  apply intervalEdge_congr_of_lt
  · simpa [sideEq] using hposition
  · intro coordinate coordinate_lt
    apply columnInterior_seed_eq_selectedBorder
    · exact hx
    · simpa [sideEq] using coordinate_lt

theorem horizontalEdge_seed_pair_iff
    (level : Nat) (i j : Fin (side level)) :
    horizontalEdge level seedNode j i = .none ∧
        horizontalEdge level seedNode j (i.val + 1) = .none ↔
      isHorizontalCarrier level i j = true := by
  have sideEq : side level = 2 * scale level := by
    rfl
  rw [horizontalEdge_seed_eq_selectedBorder_intervalEdge
      level j i j.isLt i.isLt.le,
    horizontalEdge_seed_eq_selectedBorder_intervalEdge
      level j (i.val + 1) j.isLt (by omega)]
  apply intervalEdge_pair_iff_horizontalCarrier
  simpa [sideEq] using i.isLt

theorem verticalEdge_seed_pair_iff
    (level : Nat) (i j : Fin (side level)) :
    verticalEdge level seedNode i j = .none ∧
        verticalEdge level seedNode i (j.val + 1) = .none ↔
      isVerticalCarrier level i j = true := by
  have sideEq : side level = 2 * scale level := by
    rfl
  rw [verticalEdge_seed_eq_selectedBorder_intervalEdge
      level i j i.isLt j.isLt.le,
    verticalEdge_seed_eq_selectedBorder_intervalEdge
      level i (j.val + 1) i.isLt (by omega)]
  simpa only [isVerticalCarrier, isHorizontalCarrier] using
    (intervalEdge_pair_iff_horizontalCarrier
      (level := level) (coordinate := j.val) (transverse := i.val)
      (by simpa [sideEq] using j.isLt))

theorem eraseCorner_eq_carrierRole_of_carriers
    (level x y : Nat) (role : RouteRole)
    (horizontal : role.isHorizontalCarrier =
      isHorizontalCarrier level x y)
    (vertical : role.isVerticalCarrier =
      isVerticalCarrier level x y) :
    eraseCorner role = carrierRole level x y := by
  cases role <;>
    cases horizontalCarrier : isHorizontalCarrier level x y <;>
    cases verticalCarrier : isVerticalCarrier level x y <;>
    simp_all [eraseCorner, carrierRole, RouteRole.isHorizontalCarrier,
      RouteRole.isVerticalCarrier]

/-- The corner bit aside, the routed role of every concrete seed-supertiling
site is exactly the arithmetic hierarchy role used by the addressing proof. -/
theorem eraseCorner_role_tileRectangle_seed_eq_carrierRole
    (level : Nat) (i j : Fin (side level)) :
    eraseCorner (ShadedSignals.routedScaffold.role
        (tileRectangle level seedNode i j)) =
      carrierRole level i j := by
  let role := ShadedSignals.routedScaffold.role
    (tileRectangle level seedNode i j)
  have horizontal : role.isHorizontalCarrier =
      isHorizontalCarrier level i j := by
    apply Bool.eq_iff_iff.mpr
    exact (isHorizontalCarrier_tileRectangle_iff level seedNode i j).trans
      (horizontalEdge_seed_pair_iff level i j)
  have vertical : role.isVerticalCarrier =
      isVerticalCarrier level i j := by
    apply Bool.eq_iff_iff.mpr
    exact (isVerticalCarrier_tileRectangle_iff level seedNode i j).trans
      (verticalEdge_seed_pair_iff level i j)
  exact eraseCorner_eq_carrierRole_of_carriers level i j role
    horizontal vertical

end ShadedCarrierConcreteRoles
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

end
