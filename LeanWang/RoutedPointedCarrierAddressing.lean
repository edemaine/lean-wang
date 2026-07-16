/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.RoutedPointedCarrierSquareLabeling

/-!
# Addressed routed carrier squares

An addressed carrier square assigns a logical payload coordinate to every
active crossing.  A horizontal or vertical channel stores the coordinate just
before the single logical step transmitted by that channel run.  Simple local
address equations then generate the symbolic edge labels required by
`SquarePotential`.
-/

namespace LeanWang
namespace RoutedPointedCarrierAddressing

open RoutedPointedCarrierSquareLabeling
open RoutedPointedCoreLabeling

def horizontalSuccessor (point : Int × Int) : Int × Int :=
  (point.1 + 1, point.2)

def verticalSuccessor (point : Int × Int) : Int × Int :=
  (point.1, point.2 + 1)

/-- Address presented on the east side of a horizontal carrier. -/
def horizontalOutgoing (role : RouteRole) (point source : Int × Int) :
    Int × Int :=
  match role with
  | .active | .corner => point
  | .horizontal => source
  | .inactive | .vertical => (0, 0)

/-- Address presented on the north side of a vertical carrier. -/
def verticalOutgoing (role : RouteRole) (point source : Int × Int) :
    Int × Int :=
  match role with
  | .active | .corner => point
  | .vertical => source
  | .inactive | .horizontal => (0, 0)

/-- A finite routed scaffold square with integer addresses on crossings and
channel runs. -/
structure SquareAddressing (S : RoutedScaffold) (n : Nat) where
  base : Rectangle n n
  base_valid : ValidRectangle S.tiles base
  point : Fin n → Fin n → Int × Int
  horizontalSource : Fin n → Fin n → Int × Int
  verticalSource : Fin n → Fin n → Int × Int
  corner_zero : ∀ i j, S.role (base i j) = .corner → point i j = (0, 0)
  hstep :
    ∀ i j, ∀ hi : i.val + 1 < n,
      (S.role (base i j)).isHorizontalCarrier = true →
      (S.role (base ⟨i.val + 1, hi⟩ j)).isHorizontalCarrier = true →
      let outgoing := horizontalOutgoing (S.role (base i j))
        (point i j) (horizontalSource i j)
      match S.role (base ⟨i.val + 1, hi⟩ j) with
      | .active | .corner =>
          point ⟨i.val + 1, hi⟩ j = horizontalSuccessor outgoing
      | .horizontal => horizontalSource ⟨i.val + 1, hi⟩ j = outgoing
      | .inactive | .vertical => False
  vstep :
    ∀ i j, ∀ hj : j.val + 1 < n,
      (S.role (base i j)).isVerticalCarrier = true →
      (S.role (base i ⟨j.val + 1, hj⟩)).isVerticalCarrier = true →
      let outgoing := verticalOutgoing (S.role (base i j))
        (point i j) (verticalSource i j)
      match S.role (base i ⟨j.val + 1, hj⟩) with
      | .active | .corner =>
          point i ⟨j.val + 1, hj⟩ = verticalSuccessor outgoing
      | .vertical => verticalSource i ⟨j.val + 1, hj⟩ = outgoing
      | .inactive | .horizontal => False

namespace SquareAddressing

variable {S : RoutedScaffold} {n : Nat}

set_option linter.flexible false in
/-- Convert address propagation into the symbolic labels consumed by the
generic pointed-plane realization theorem. -/
def toSquarePotential (addressing : SquareAddressing S n) :
    SquarePotential S n where
  base := addressing.base
  base_valid := addressing.base_valid
  point := addressing.point
  horizontal := fun i j => .east (addressing.horizontalSource i j)
  vertical := fun i j => .north (addressing.verticalSource i j)
  corner_zero := addressing.corner_zero
  hcompatible := by
    intro i j hi hleft hright
    have step := addressing.hstep i j hi hleft hright
    cases leftRole : S.role (addressing.base i j) <;>
      cases rightRole : S.role
        (addressing.base ⟨i.val + 1, hi⟩ j) <;>
      simp_all [RouteRole.isHorizontalCarrier, horizontalOutgoing,
        horizontalSuccessor]
    all_goals first
      | exact EdgeLabel.Compatible.refl _
      | exact EdgeLabel.Compatible.horizontal _
  vcompatible := by
    intro i j hj hlower hupper
    have step := addressing.vstep i j hj hlower hupper
    cases lowerRole : S.role (addressing.base i j) <;>
      cases upperRole : S.role
        (addressing.base i ⟨j.val + 1, hj⟩) <;>
      simp_all [RouteRole.isVerticalCarrier, verticalOutgoing,
        verticalSuccessor]
    all_goals first
      | exact EdgeLabel.Compatible.refl _
      | exact EdgeLabel.Compatible.vertical _

end SquareAddressing

/-- Cofinal addressed squares realize every pointed payload plane. -/
theorem realizesRoutedPointedPlanes_of_cofinalAddressings
    {S : RoutedScaffold}
    (addressings : ∀ n : Nat,
      ∃ N : Nat, n ≤ N ∧ Nonempty (SquareAddressing S N)) :
    RealizesRoutedPointedPlanes S :=
  realizesRoutedPointedPlanes_of_cofinalSquares fun n => by
    rcases addressings n with ⟨N, hnN, ⟨addressing⟩⟩
    exact ⟨N, hnN, ⟨addressing.toSquarePotential⟩⟩

end RoutedPointedCarrierAddressing
end LeanWang
