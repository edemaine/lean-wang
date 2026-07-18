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

private theorem CycleShade.nearest_above_selected_north
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row boundary : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hrowBoundary : row < boundary)
    (hboundaryNorth : boundary < quarterNorth north)
    (free : IsFreeRow indexGrid stateGrid west east row)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (hbetween : forall y, row < y -> y < boundary ->
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (stateGrid column y) = none) :
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) = some .north := by
  apply OrientedLightBoundarySearch.selected_after_eq_of_negative_rejected
    (selected := fun y => ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column y) (quadrantAt column y)
      (stateGrid column y))
    (primary := fun scan y => rightWeightAt stateGrid scan y)
    (secondary := fun scan y => leftWeightAt stateGrid scan y)
    (potential := fun scan y => faceHeight stateGrid scan (quarterSouth south)
      (y - quarterSouth south))
    (coordinate := column) (start := row) (boundary := boundary)
    (expected := .north) (rejected := .south)
  · intro direction
    cases direction <;> simp
  · omega
  · exact hrowBoundary
  · exact hselected
  · exact ValidShadeGrid.horizontal_south_has_negative_weightAt valid
  · exact fun scan y =>
      OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
        valid scan y
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
      shaded cycle valid (column := scan) (row := row)
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (le_of_lt hsouth) (hrowBoundary.trans hboundaryNorth) free
  · intro scan position scanEq lower upper
    exact faceHeight_step_up (by omega)
  · intro y hyRow hyBoundary
    exact ValidShadeGrid.horizontal_none_weightsAt_zero valid
      (hbetween y hyRow hyBoundary)
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
      shaded cycle valid
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (row := boundary) (by omega) hboundaryNorth

private theorem CycleShade.nearest_below_selected_south
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row boundary : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hboundarySouth : quarterSouth south < boundary)
    (hboundaryRow : boundary < row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeRow indexGrid stateGrid west east row)
    (hat : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column row) (quadrantAt column row)
      (stateGrid column row) = none)
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) ≠ none)
    (hbetween : forall y, boundary < y -> y < row ->
      ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (stateGrid column y) = none) :
    ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) = some .south := by
  apply OrientedLightBoundarySearch.selected_before_eq_of_positive_rejected
    (selected := fun y => ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column y) (quadrantAt column y)
      (stateGrid column y))
    (primary := fun scan y => rightWeightAt stateGrid scan y)
    (secondary := fun scan y => leftWeightAt stateGrid scan y)
    (potential := fun scan y => faceHeight stateGrid scan (quarterSouth south)
      (y - quarterSouth south))
    (coordinate := column) (boundary := boundary) (finish := row)
    (expected := .south) (rejected := .north)
  · intro direction
    cases direction <;> simp
  · omega
  · omega
  · exact hselected
  · exact ValidShadeGrid.horizontal_north_has_positive_weightAt valid
  · exact fun scan y =>
      OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
        valid scan y
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
      shaded cycle valid (column := scan) (row := row)
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (by omega) hnorth free
  · intro scan position scanEq lower upper
    exact faceHeight_step_up (by omega)
  · intro y hyBoundary hyRow
    have hnone : ShadedSignals.selectedHorizontalFor
        (componentAt indexGrid column y) (quadrantAt column y)
        (stateGrid column y) = none :=
      if hy : y = row then by simpa [hy] using hat
      else hbetween y hyBoundary (lt_of_le_of_ne hyRow hy)
    exact ValidShadeGrid.horizontal_none_weightsAt_zero valid hnone
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
      shaded cycle valid
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)
      (row := boundary - 1) (by omega) (by omega)

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
  apply OrientedLightBoundarySearch.boundary_of_exists_selected witness
  · intro boundary rowBoundary boundaryNorth boundarySelected between
    exact CycleShade.nearest_above_selected_north
      shaded cycle valid hwest heast hsouth rowBoundary boundaryNorth free
      boundarySelected between
  · intro boundary boundarySouth boundaryRow boundarySelected between rowClear
    exact CycleShade.nearest_below_selected_south
      shaded cycle valid hwest heast boundarySouth boundaryRow hnorth free
      rowClear boundarySelected between

end OrientedLightVerticalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
