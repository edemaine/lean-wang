/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightVerticalGeometry

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

theorem ValidShadeGrid.vertical_west_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .west) :
    Or (upWeightAt stateGrid x y = -1)
      (downWeightAt stateGrid x y = -1) := by
  simpa [upWeightAt, downWeightAt] using
    vertical_west_has_negative_weight _ _ _
      (valid.allowed x y) hselected

theorem ValidShadeGrid.vertical_east_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .east) :
    Or (upWeightAt stateGrid x y = 1)
      (downWeightAt stateGrid x y = 1) := by
  simpa [upWeightAt, downWeightAt] using
    vertical_east_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem negative_upWeightAt_right_false
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {start row boundary : Nat}
    (hstartWest : quarterWest west <= start)
    (hstartBoundary : start < boundary)
    (hboundaryEast : boundary < quarterEast east)
    (hrowSouth : quarterSouth south <= row)
    (hrowNorth : row < quarterNorth north)
    (hfreeHeight : faceHeight stateGrid start (quarterSouth south)
      (row - quarterSouth south) = 1)
    (hzero : forall x, start < x -> x < boundary ->
      upWeightAt stateGrid x row = 0)
    (hnegative : upWeightAt stateGrid boundary row = -1) : False := by
  let offset := row - quarterSouth south
  let potential := fun x =>
    faceHeight stateGrid x (quarterSouth south) offset
  let weight := fun x => upWeightAt stateGrid x row
  have hrow : quarterSouth south + offset = row := by
    dsimp [offset]
    omega
  have step (position : Nat) (westPosition : quarterWest west < position)
      (eastPosition : position < quarterEast east) :
      potential position = potential (position - 1) + weight position := by
    have difference := OrientedLightHeight.CycleShade.faceHeight_sub_left
      shaded cycle valid (column := position) (offset := offset)
        westPosition eastPosition
    rw [hrow] at difference
    dsimp [potential, weight]
    omega
  apply OrientedLightBoundarySearch.negative_step_after_false
    (potential := potential) (weight := weight) hstartBoundary
    (by simpa [potential] using hfreeHeight)
    (fun position lower upper => step position (by omega) (by omega))
    (fun position lower upper => by simpa [weight] using hzero position lower upper)
    (by simpa [weight] using hnegative)
  exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid (column := boundary) (row := row)
      (by omega) hboundaryEast hrowSouth hrowNorth

private theorem positive_upWeightAt_left_false
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {finish row boundary : Nat}
    (hboundaryWest : quarterWest west < boundary)
    (hboundaryFinish : boundary <= finish)
    (hfinishEast : finish < quarterEast east)
    (hrowSouth : quarterSouth south <= row)
    (hrowNorth : row < quarterNorth north)
    (hfreeHeight : faceHeight stateGrid finish (quarterSouth south)
      (row - quarterSouth south) = 1)
    (hzero : forall x, boundary < x -> x <= finish ->
      upWeightAt stateGrid x row = 0)
    (hpositiveWeight : upWeightAt stateGrid boundary row = 1) : False := by
  let offset := row - quarterSouth south
  let potential := fun x =>
    faceHeight stateGrid x (quarterSouth south) offset
  let weight := fun x => upWeightAt stateGrid x row
  have hrow : quarterSouth south + offset = row := by
    dsimp [offset]
    omega
  have step (position : Nat) (westPosition : quarterWest west < position)
      (eastPosition : position < quarterEast east) :
      potential position = potential (position - 1) + weight position := by
    have difference := OrientedLightHeight.CycleShade.faceHeight_sub_left
      shaded cycle valid (column := position) (offset := offset)
        westPosition eastPosition
    rw [hrow] at difference
    dsimp [potential, weight]
    omega
  apply OrientedLightBoundarySearch.positive_step_before_false
    (potential := potential) (weight := weight) hboundaryFinish
    (by simpa [potential] using hfreeHeight)
    (step boundary hboundaryWest (by omega))
    (fun position lower upper => step position (by omega) (by omega))
    (fun position lower upper => by simpa [weight] using hzero position lower upper)
    (by simpa [weight] using hpositiveWeight)
  exact OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid (column := boundary - 1) (row := row)
      (by omega) (by omega) hrowSouth hrowNorth

theorem CycleShade.nearest_right_selected_east
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row boundary : Nat}
    (hwest : quarterWest west < column)
    (hcolumnBoundary : column < boundary)
    (hboundaryEast : boundary < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (hbetween : forall x, column < x -> x < boundary ->
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x row) (quadrantAt x row)
        (stateGrid x row) = none) :
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) = some .east := by
  cases hvalue : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) with
  | none => contradiction
  | some interior =>
      cases interior with
      | east => rfl
      | west =>
          have hweights :=
            ValidShadeGrid.vertical_west_has_negative_weightAt valid hvalue
          rcases hweights with hup | hdown
          · have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_right_of_freeColumn
                shaded cycle valid
                (column := column) (row := row) (le_of_lt hwest)
                (hcolumnBoundary.trans hboundaryEast) (le_of_lt hsouth)
                hnorth free
            exact False.elim (negative_upWeightAt_right_false
              shaded cycle valid (start := column) (row := row)
              (boundary := boundary) (le_of_lt hwest) hcolumnBoundary
              hboundaryEast (le_of_lt hsouth) hnorth hfree
              (fun x hxColumn hxBoundary =>
                (ValidShadeGrid.vertical_none_weightsAt_zero valid
                  (hbetween x hxColumn hxBoundary)).1) hup)
          · have hshared :=
              OrientedLightHeight.ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
                valid boundary (row - 1)
            have hrow : row - 1 + 1 = row := by omega
            rw [hrow, hdown] at hshared
            have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_right_of_freeColumn
                shaded cycle valid
                (column := column) (row := row - 1) (le_of_lt hwest)
                (hcolumnBoundary.trans hboundaryEast) (by omega)
                (by omega) free
            exact False.elim (negative_upWeightAt_right_false
              shaded cycle valid (start := column) (row := row - 1)
              (boundary := boundary) (le_of_lt hwest) hcolumnBoundary
              hboundaryEast (by omega) (by omega) hfree
              (fun x hxColumn hxBoundary => by
                have hzero := ValidShadeGrid.vertical_none_weightsAt_zero
                  valid (hbetween x hxColumn hxBoundary)
                have hmatch :=
                  OrientedLightHeight.ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
                    valid x (row - 1)
                rw [hrow, hzero.2] at hmatch
                exact hmatch) hshared)

theorem CycleShade.nearest_left_selected_west
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row boundary : Nat}
    (hboundaryWest : quarterWest west < boundary)
    (hboundaryColumn : boundary < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south < row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column)
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) ≠ none)
    (hbetween : forall x, boundary < x -> x < column ->
      ShadedSignals.selectedVerticalFor
        (componentAt indexGrid x row) (quadrantAt x row)
        (stateGrid x row) = none) :
    ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) = some .west := by
  cases hvalue : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid boundary row) (quadrantAt boundary row)
      (stateGrid boundary row) with
  | none => contradiction
  | some interior =>
      cases interior with
      | west => rfl
      | east =>
          have hweights :=
            ValidShadeGrid.vertical_east_has_positive_weightAt valid hvalue
          rcases hweights with hup | hdown
          · have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_left_of_freeColumn
                shaded cycle valid
                (column := column) (row := row) (by omega) heast
                (le_of_lt hsouth) hnorth free
            exact False.elim (positive_upWeightAt_left_false
              shaded cycle valid (finish := column - 1) (row := row)
              (boundary := boundary) hboundaryWest (by omega) (by omega)
              (le_of_lt hsouth) hnorth hfree
              (fun x hxBoundary hxFinish =>
                (ValidShadeGrid.vertical_none_weightsAt_zero valid
                  (hbetween x hxBoundary (by omega))).1) hup)
          · have hshared :=
              OrientedLightHeight.ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
                valid boundary (row - 1)
            have hrow : row - 1 + 1 = row := by omega
            rw [hrow, hdown] at hshared
            have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_left_of_freeColumn
                shaded cycle valid
                (column := column) (row := row - 1) (by omega) heast
                (by omega) (by omega) free
            exact False.elim (positive_upWeightAt_left_false
              shaded cycle valid (finish := column - 1) (row := row - 1)
              (boundary := boundary) hboundaryWest (by omega) (by omega)
              (by omega) (by omega) hfree
              (fun x hxBoundary hxFinish => by
                have hzero := ValidShadeGrid.vertical_none_weightsAt_zero
                  valid (hbetween x hxBoundary (by omega))
                have hmatch :=
                  OrientedLightHeight.ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
                    valid x (row - 1)
                rw [hrow, hzero.2] at hmatch
                exact hmatch) hshared)

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
  apply OrientedLightBoundarySearch.boundary_of_exists_selected witness
  · intro boundary columnBoundary boundaryEast boundarySelected between
    exact CycleShade.nearest_right_selected_east
      shaded cycle valid hwest columnBoundary boundaryEast hsouth hnorth free
      boundarySelected between
  · intro boundary boundaryWest boundaryColumn boundarySelected between _
    exact CycleShade.nearest_left_selected_west
      shaded cycle valid boundaryWest boundaryColumn heast hsouth hnorth free
      boundarySelected between

end OrientedLightHorizontalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
