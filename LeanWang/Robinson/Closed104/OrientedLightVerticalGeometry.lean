/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightFreeHeight
import LeanWang.Robinson.Closed104.OrientedLightBoundarySearch
import LeanWang.Robinson.Closed104.ShadedObstructionGeometry

/-!
# Vertical nearest-boundary geometry from light-wire height

Above a free row, the nearest selected horizontal boundary points east and is
therefore labeled `north`.  Below it, the nearest boundary points west and is
labeled `south`.  A boundary with the opposite orientation would change the
unit face height to zero, contradicting the height minimum principle.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightVerticalGeometry

open OrientedRedCycles RedShadeCycles RedShadePaths ShadedPlaneSignalGrid
  OrientedLightHeightWeights OrientedLightHeight OrientedLightFreeHeight
  Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

private theorem ValidShadeGrid.horizontal_south_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .south) :
    Or (rightWeightAt stateGrid x y = -1)
      (leftWeightAt stateGrid x y = -1) := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_south_has_negative_weight _ _ _
      (valid.allowed x y) hselected

private theorem ValidShadeGrid.horizontal_north_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .north) :
    Or (rightWeightAt stateGrid x y = 1)
      (leftWeightAt stateGrid x y = 1) := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_north_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem faceHeight_step_up {scan position : Nat}
    (southPosition : quarterSouth south < position) :
    faceHeight stateGrid scan (quarterSouth south)
        (position - quarterSouth south) =
      faceHeight stateGrid scan (quarterSouth south)
          (position - 1 - quarterSouth south) +
        rightWeightAt stateGrid scan position := by
  have offset : position - quarterSouth south =
      (position - 1 - quarterSouth south) + 1 := by omega
  rw [offset, faceHeight]
  congr 2
  omega

/-- Vertical half of the Robinson obstruction geometry, now derived directly
from the height minimum principle. -/
theorem CycleShade.verticalBoundary
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    forall {column row : Nat},
      quarterWest west < column -> column < quarterEast east ->
      quarterSouth south < row -> row < quarterNorth north ->
      IsFreeRow indexGrid stateGrid west east row ->
      Not (IsFreeColumn indexGrid stateGrid south north column) ->
        ShadedSignals.selectedHorizontalFor
            (componentAt indexGrid column row) (quadrantAt column row)
            (stateGrid column row) ≠ none \/
        (exists boundary, row < boundary /\ boundary < quarterNorth north /\
          ShadedSignals.selectedHorizontalFor
            (componentAt indexGrid column boundary) (quadrantAt column boundary)
            (stateGrid column boundary) = some .north /\
          forall y, row < y -> y < boundary ->
            ShadedSignals.selectedHorizontalFor
              (componentAt indexGrid column y) (quadrantAt column y)
              (stateGrid column y) = none) \/
        (exists boundary, quarterSouth south < boundary /\ boundary < row /\
          ShadedSignals.selectedHorizontalFor
            (componentAt indexGrid column boundary) (quadrantAt column boundary)
            (stateGrid column boundary) = some .south /\
          forall y, boundary < y -> y < row ->
            ShadedSignals.selectedHorizontalFor
              (componentAt indexGrid column y) (quadrantAt column y)
              (stateGrid column y) = none) := by
  intro column row hwest heast hsouth hnorth free notFree
  let selected := fun y =>
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column y) (quadrantAt column y)
      (stateGrid column y)
  have witness : exists boundary,
      quarterSouth south < boundary /\ boundary < quarterNorth north /\
        selected boundary ≠ none := by
    simp only [IsFreeColumn] at notFree
    push Not at notFree
    exact notFree
  apply OrientedLightBoundarySearch.boundary_of_unit_height
    (selected := selected)
    (primary := fun scan y => rightWeightAt stateGrid scan y)
    (secondary := fun scan y => leftWeightAt stateGrid scan y)
    (potential := fun scan y => faceHeight stateGrid scan (quarterSouth south)
      (y - quarterSouth south))
    (lower := quarterSouth south) (point := row)
    (upper := quarterNorth north) (scanCoordinate := column)
    (beforeFinish := row)
    (after := .north) (before := .south)
    (rejectedAfter := .south) (rejectedBefore := .north) witness
  · intro direction
    cases direction <;> simp
  · intro direction
    cases direction <;> simp
  · omega
  · exact ⟨hsouth, hnorth⟩
  · omega
  · exact hnorth
  · omega
  · intro boundary rejected
    exact ValidShadeGrid.horizontal_south_has_negative_weightAt valid rejected
  · intro boundary rejected
    exact ValidShadeGrid.horizontal_north_has_positive_weightAt valid rejected
  · exact fun scan y =>
      OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
        valid scan y
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
      shaded cycle valid (column := scan) (row := row)
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (le_of_lt hsouth) hnorth free
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
      shaded cycle valid (column := scan) (row := row)
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (le_of_lt hsouth) hnorth free
  · intro scan position scanEq positionSouth positionNorth
    exact faceHeight_step_up positionSouth
  · intro position clear
    exact ValidShadeGrid.horizontal_none_weightsAt_zero valid clear
  · intro scan position scanEq positionSouth positionNorth
    exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
      shaded cycle valid
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (row := position) positionSouth positionNorth

end OrientedLightVerticalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
