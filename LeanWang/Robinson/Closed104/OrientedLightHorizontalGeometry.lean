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

/-- Zero vertical crossings preserve height while moving horizontally. -/
private theorem faceHeight_add_column_eq_of_upWeightAt_zero
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {start offset count : Nat}
    (hstartWest : quarterWest west <= start)
    (hfinishEast : start + count < quarterEast east)
    (hzero : forall i, i < count ->
      upWeightAt stateGrid (start + i + 1)
        (quarterSouth south + offset) = 0) :
    faceHeight stateGrid (start + count) (quarterSouth south) offset =
      faceHeight stateGrid start (quarterSouth south) offset := by
  induction count with
  | zero => simp
  | succ count ih =>
      have hprevious := ih (by omega) (fun i hi => hzero i (by omega))
      have hdiff := OrientedLightHeight.CycleShade.faceHeight_sub_left
        shaded cycle valid (column := start + (count + 1))
        (offset := offset) (by omega) (by omega)
      have hleft : start + (count + 1) - 1 = start + count := by omega
      rw [hleft] at hdiff
      have hstep := hzero count (by omega)
      have hcolumn : start + count + 1 = start + (count + 1) := by omega
      rw [hcolumn] at hstep
      omega

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
  let count := boundary - start - 1
  have hrow : quarterSouth south + offset = row := by
    dsimp [offset]
    omega
  have hrun := faceHeight_add_column_eq_of_upWeightAt_zero
    shaded cycle valid (start := start) (offset := offset) (count := count)
    hstartWest (by dsimp [count]; omega) (by
      intro i hi
      rw [hrow]
      apply hzero (start + i + 1)
      · omega
      · dsimp [count] at hi
        omega)
  have hbeforeColumn : start + count = boundary - 1 := by
    dsimp [count]
    omega
  rw [hbeforeColumn, hfreeHeight] at hrun
  have hbefore : faceHeight stateGrid (boundary - 1)
      (quarterSouth south) offset = 1 := hrun
  have hdiff := OrientedLightHeight.CycleShade.faceHeight_sub_left
    shaded cycle valid (column := boundary) (offset := offset)
      (by omega) hboundaryEast
  have hleft : boundary - 1 = boundary - 1 := rfl
  rw [hrow, hnegative, hbefore] at hdiff
  have hafter : faceHeight stateGrid boundary (quarterSouth south) offset = 0 := by
    omega
  have hpositive := OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid (column := boundary) (row := row)
      (by omega) hboundaryEast hrowSouth hrowNorth
  rw [hafter] at hpositive
  omega

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
  let count := finish - boundary
  have hrow : quarterSouth south + offset = row := by
    dsimp [offset]
    omega
  have hrun := faceHeight_add_column_eq_of_upWeightAt_zero
    shaded cycle valid (start := boundary) (offset := offset) (count := count)
    (le_of_lt hboundaryWest) (by dsimp [count]; omega) (by
      intro i hi
      rw [hrow]
      apply hzero (boundary + i + 1)
      · omega
      · dsimp [count] at hi
        omega)
  have hfinish : boundary + count = finish := by
    dsimp [count]
    omega
  rw [hfinish, hfreeHeight] at hrun
  have hboundaryHeight : faceHeight stateGrid boundary
      (quarterSouth south) offset = 1 := hrun.symm
  have hdiff := OrientedLightHeight.CycleShade.faceHeight_sub_left
    shaded cycle valid (column := boundary) (offset := offset)
      hboundaryWest (hboundaryFinish.trans_lt hfinishEast)
  rw [hrow, hpositiveWeight, hboundaryHeight] at hdiff
  have hleftHeight : faceHeight stateGrid (boundary - 1)
      (quarterSouth south) offset = 0 := by omega
  have hpositive := OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid (column := boundary - 1) (row := row)
      (by omega) (by omega) hrowSouth hrowNorth
  rw [hleftHeight] at hpositive
  omega

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
  by_cases hat : selected column ≠ none
  · exact Or.inl hat
  have witness : exists boundary,
      quarterWest west < boundary /\ boundary < quarterEast east /\
        selected boundary ≠ none := by
    simp only [IsFreeRow] at notFree
    push Not at notFree
    exact notFree
  rcases witness with ⟨boundary, hboundaryWest, hboundaryEast, hselected⟩
  rcases lt_trichotomy column boundary with hright | hequal | hleft
  · rcases OrientedLightVerticalGeometry.exists_first_after
      (P := fun x => selected x ≠ none) hright hselected with
      ⟨first, hcolumnFirst, hfirstBoundary, hfirstSelected, hbetween⟩
    have hfirstEast := hfirstBoundary.trans_lt hboundaryEast
    have horiented := CycleShade.nearest_right_selected_east
      shaded cycle valid hwest hcolumnFirst hfirstEast hsouth hnorth free
      hfirstSelected (fun x hxColumn hxFirst =>
        not_ne_iff.mp (hbetween x hxColumn hxFirst))
    exact Or.inr (Or.inl ⟨first, hcolumnFirst, hfirstEast, horiented,
      fun x hxColumn hxFirst => not_ne_iff.mp (hbetween x hxColumn hxFirst)⟩)
  · subst boundary
    exact False.elim (hselected (not_ne_iff.mp hat))
  · rcases OrientedLightVerticalGeometry.exists_last_before
      (P := fun x => selected x ≠ none) hleft hselected with
      ⟨last, hboundaryLast, hlastColumn, hlastSelected, hbetween⟩
    have hlastWest := hboundaryWest.trans_le hboundaryLast
    have horiented := CycleShade.nearest_left_selected_west
      shaded cycle valid hlastWest hlastColumn heast hsouth hnorth free
      hlastSelected (fun x hxLast hxColumn =>
        not_ne_iff.mp (hbetween x hxLast hxColumn))
    exact Or.inr (Or.inr ⟨last, hlastWest, hlastColumn, horiented,
      fun x hxLast hxColumn => not_ne_iff.mp (hbetween x hxLast hxColumn)⟩)

end OrientedLightHorizontalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
