/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightFreeHeight
import LeanWang.Robinson.Closed104.OrientedLightBoundarySearch
import LeanWang.Robinson.Closed104.ShadedObstructionGeometry

/-!
# Horizontal nearest-boundary geometry from light-wire height

To the right of a free column, the nearest selected vertical boundary points
south and is labeled `east`.  To the left, it points north and is labeled
`west`.  This is the horizontal dual of the vertical height argument, using
the same face height rather than a separately rotated construction.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightHorizontalGeometry

open OrientedRedCycles RedShadeCycles RedShadePaths ShadedPlaneSignalGrid
  OrientedLightHeightWeights OrientedLightHeight OrientedLightFreeHeight
  Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

private theorem ValidShadeGrid.vertical_west_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .west) :
    Or (upWeightAt stateGrid x y = -1)
      (downWeightAt stateGrid x y = -1) := by
  simpa [upWeightAt, downWeightAt] using
    vertical_west_has_negative_weight _ _ _
      (valid.allowed x y) hselected

private theorem ValidShadeGrid.vertical_east_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .east) :
    Or (upWeightAt stateGrid x y = 1)
      (downWeightAt stateGrid x y = 1) := by
  simpa [upWeightAt, downWeightAt] using
    vertical_east_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem faceHeight_step_right
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {row position : Nat} (rowSouth : quarterSouth south ≤ row)
    (westPosition : quarterWest west < position)
    (eastPosition : position < quarterEast east) :
    faceHeight stateGrid position (quarterSouth south)
        (row - quarterSouth south) =
      faceHeight stateGrid (position - 1) (quarterSouth south)
          (row - quarterSouth south) + upWeightAt stateGrid position row := by
  have difference := OrientedLightHeight.CycleShade.faceHeight_sub_left
    shaded cycle valid (column := position)
      (offset := row - quarterSouth south) westPosition eastPosition
  rw [show quarterSouth south + (row - quarterSouth south) = row by omega]
    at difference
  omega

/-- Horizontal half of the Robinson obstruction geometry. -/
theorem CycleShade.horizontalBoundary
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid) :
    forall {column row : Nat},
      quarterWest west < column -> column < quarterEast east ->
      quarterSouth south < row -> row < quarterNorth north ->
      IsFreeColumn indexGrid stateGrid south north column ->
      Not (IsFreeRow indexGrid stateGrid west east row) ->
        ShadedSignals.selectedVerticalFor
            (componentAt indexGrid column row) (quadrantAt column row)
            (stateGrid column row) ≠ none \/
        (exists boundary, column < boundary /\ boundary < quarterEast east /\
          ShadedSignals.selectedVerticalFor
            (componentAt indexGrid boundary row) (quadrantAt boundary row)
            (stateGrid boundary row) = some .east /\
          forall x, column < x -> x < boundary ->
            ShadedSignals.selectedVerticalFor
              (componentAt indexGrid x row) (quadrantAt x row)
              (stateGrid x row) = none) \/
        (exists boundary, quarterWest west < boundary /\ boundary < column /\
          ShadedSignals.selectedVerticalFor
            (componentAt indexGrid boundary row) (quadrantAt boundary row)
            (stateGrid boundary row) = some .west /\
          forall x, boundary < x -> x < column ->
            ShadedSignals.selectedVerticalFor
              (componentAt indexGrid x row) (quadrantAt x row)
              (stateGrid x row) = none) := by
  intro column row hwest heast hsouth hnorth free notFree
  let selected := fun x => ShadedSignals.selectedVerticalFor
    (componentAt indexGrid x row) (quadrantAt x row) (stateGrid x row)
  have witness : exists boundary,
      quarterWest west < boundary /\ boundary < quarterEast east /\
        selected boundary ≠ none := by
    simp only [IsFreeRow] at notFree
    push Not at notFree
    exact notFree
  apply OrientedLightBoundarySearch.boundary_of_unit_height
    (selected := selected)
    (primary := fun scan x => upWeightAt stateGrid x scan)
    (secondary := fun scan x => downWeightAt stateGrid x scan)
    (potential := fun scan x => faceHeight stateGrid x (quarterSouth south)
      (scan - quarterSouth south))
    (lower := quarterWest west) (point := column)
    (upper := quarterEast east) (scanCoordinate := row)
    (beforeFinish := column - 1)
    (after := .east) (before := .west)
    (rejectedAfter := .west) (rejectedBefore := .east) witness
  · intro direction
    cases direction <;> simp
  · intro direction
    cases direction <;> simp
  · omega
  · exact ⟨hwest, heast⟩
  · omega
  · omega
  · omega
  · intro boundary rejected
    exact ValidShadeGrid.vertical_west_has_negative_weightAt valid rejected
  · intro boundary rejected
    exact ValidShadeGrid.vertical_east_has_positive_weightAt valid rejected
  · exact fun scan x =>
      OrientedLightHeight.ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
        valid x scan
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_right_of_freeColumn
      shaded cycle valid (column := column) (row := scan)
      (le_of_lt hwest) heast
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega) free
  · intro scan scanEq
    exact OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_left_of_freeColumn
      shaded cycle valid (column := column) (row := scan)
      hwest heast
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega) free
  · intro scan position scanEq positionWest positionEast
    exact faceHeight_step_right shaded cycle valid
      (by rcases scanEq with h | h <;> omega) positionWest positionEast
  · intro position clear
    exact ValidShadeGrid.vertical_none_weightsAt_zero valid clear
  · intro scan position scanEq positionWest positionEast
    exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
      shaded cycle valid (column := position) (row := scan)
      positionWest positionEast
      (by rcases scanEq with h | h <;> omega)
      (by rcases scanEq with h | h <;> omega)

end OrientedLightHorizontalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
