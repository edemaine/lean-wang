/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightFreeHeight
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

theorem ValidShadeGrid.horizontal_south_has_negative_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .south) :
    Or (rightWeightAt stateGrid x y = -1)
      (leftWeightAt stateGrid x y = -1) := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_south_has_negative_weight _ _ _
      (valid.allowed x y) hselected

theorem ValidShadeGrid.horizontal_north_has_positive_weightAt
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) =
        some .north) :
    Or (rightWeightAt stateGrid x y = 1)
      (leftWeightAt stateGrid x y = 1) := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_north_has_positive_weight _ _ _
      (valid.allowed x y) hselected

private theorem negative_rightWeightAt_above_false
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {scan row boundary : Nat}
    (hscanWest : quarterWest west <= scan)
    (hscanEast : scan < quarterEast east)
    (hrowSouth : quarterSouth south <= row)
    (hrowBoundary : row < boundary)
    (hboundaryNorth : boundary < quarterNorth north)
    (hfreeHeight : faceHeight stateGrid scan (quarterSouth south)
      (row - quarterSouth south) = 1)
    (hzero : forall y, row < y -> y < boundary ->
      rightWeightAt stateGrid scan y = 0)
    (hnegative : rightWeightAt stateGrid scan boundary = -1) : False := by
  let start := row - quarterSouth south
  let count := boundary - row - 1
  have hrun := faceHeight_add_eq_of_rightWeightAt_zero
    stateGrid scan (quarterSouth south) start count (by
      intro i hi
      apply hzero (quarterSouth south + (start + i) + 1)
      · dsimp [start, count] at hi ⊢
        omega
      · dsimp [start, count] at hi ⊢
        omega)
  have hoffset : start + count = boundary - quarterSouth south - 1 := by
    dsimp [start, count]
    omega
  rw [hoffset, hfreeHeight] at hrun
  have hbefore : faceHeight stateGrid scan (quarterSouth south)
      (boundary - quarterSouth south - 1) = 1 := hrun
  have hafter : faceHeight stateGrid scan (quarterSouth south)
      (boundary - quarterSouth south) = 0 := by
    have hsucc : boundary - quarterSouth south =
        (boundary - quarterSouth south - 1) + 1 := by omega
    rw [hsucc, faceHeight, hbefore]
    have hy : quarterSouth south +
        (boundary - quarterSouth south - 1) + 1 = boundary := by omega
    rw [hy, hnegative]
    omega
  have hpositive := OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid hscanWest hscanEast (row := boundary)
      (by omega) hboundaryNorth
  rw [hafter] at hpositive
  omega

private theorem positive_rightWeightAt_below_false
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {scan row boundary : Nat}
    (hscanWest : quarterWest west <= scan)
    (hscanEast : scan < quarterEast east)
    (hboundarySouth : quarterSouth south < boundary)
    (hboundaryRow : boundary < row)
    (hrowNorth : row < quarterNorth north)
    (hfreeHeight : faceHeight stateGrid scan (quarterSouth south)
      (row - quarterSouth south) = 1)
    (hzero : forall y, boundary < y -> y <= row ->
      rightWeightAt stateGrid scan y = 0)
    (hpositiveWeight : rightWeightAt stateGrid scan boundary = 1) : False := by
  let start := boundary - quarterSouth south
  let count := row - boundary
  have hrun := faceHeight_add_eq_of_rightWeightAt_zero
    stateGrid scan (quarterSouth south) start count (by
      intro i hi
      apply hzero (quarterSouth south + (start + i) + 1)
      · dsimp [start, count] at hi ⊢
        omega
      · dsimp [start, count] at hi ⊢
        omega)
  have hoffset : start + count = row - quarterSouth south := by
    dsimp [start, count]
    omega
  rw [hoffset, hfreeHeight] at hrun
  have hboundaryHeight : faceHeight stateGrid scan (quarterSouth south)
      (boundary - quarterSouth south) = 1 := hrun.symm
  have hbelow : faceHeight stateGrid scan (quarterSouth south)
      (boundary - quarterSouth south - 1) = 0 := by
    have hsucc : boundary - quarterSouth south =
        (boundary - quarterSouth south - 1) + 1 := by omega
    rw [hsucc, faceHeight] at hboundaryHeight
    have hy : quarterSouth south +
        (boundary - quarterSouth south - 1) + 1 = boundary := by omega
    rw [hy, hpositiveWeight] at hboundaryHeight
    omega
  have hpositive := OrientedLightFreeHeight.CycleShade.one_le_faceHeight_at
    shaded cycle valid hscanWest hscanEast
      (row := boundary - 1) (by omega) (by omega)
  have hrow : boundary - 1 - quarterSouth south =
      boundary - quarterSouth south - 1 := by omega
  rw [hrow, hbelow] at hpositive
  omega

theorem CycleShade.nearest_above_selected_north
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
  cases hvalue : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) with
  | none => contradiction
  | some interior =>
      cases interior with
      | north => rfl
      | south =>
          have hweights :=
            ValidShadeGrid.horizontal_south_has_negative_weightAt valid hvalue
          rcases hweights with hright | hleft
          · have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
                shaded cycle valid (column := column) (row := row)
                (le_of_lt hwest) heast (le_of_lt hsouth)
                (hrowBoundary.trans hboundaryNorth) free
            exact False.elim (negative_rightWeightAt_above_false
              shaded cycle valid (scan := column) (row := row)
              (boundary := boundary) (le_of_lt hwest) heast
              (le_of_lt hsouth) hrowBoundary hboundaryNorth hfree
              (fun y hyRow hyBoundary =>
                (ValidShadeGrid.horizontal_none_weightsAt_zero valid
                  (hbetween y hyRow hyBoundary)).1) hright)
          · have hmatch :=
              OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
                valid (column - 1) boundary
            have hcolumn : column - 1 + 1 = column := by omega
            rw [hcolumn, hleft] at hmatch
            have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
                shaded cycle valid (column := column - 1) (row := row)
                (by omega) (by omega) (le_of_lt hsouth)
                (hrowBoundary.trans hboundaryNorth) free
            exact False.elim (negative_rightWeightAt_above_false
              shaded cycle valid (scan := column - 1) (row := row)
              (boundary := boundary) (by omega) (by omega)
              (le_of_lt hsouth) hrowBoundary hboundaryNorth hfree
              (fun y hyRow hyBoundary => by
                have hzero := ValidShadeGrid.horizontal_none_weightsAt_zero
                  valid (hbetween y hyRow hyBoundary)
                have hshared :=
                  OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
                    valid (column - 1) y
                rw [hcolumn, hzero.2] at hshared
                exact hshared) hmatch)

theorem CycleShade.nearest_below_selected_south
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
  cases hvalue : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid column boundary) (quadrantAt column boundary)
      (stateGrid column boundary) with
  | none => contradiction
  | some interior =>
      cases interior with
      | south => rfl
      | north =>
          have hweights :=
            ValidShadeGrid.horizontal_north_has_positive_weightAt valid hvalue
          rcases hweights with hright | hleft
          · have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
                shaded cycle valid (column := column) (row := row)
                (le_of_lt hwest) heast (by omega) hnorth free
            exact False.elim (positive_rightWeightAt_below_false
              shaded cycle valid (scan := column) (row := row)
              (boundary := boundary) (le_of_lt hwest) heast
              hboundarySouth hboundaryRow hnorth hfree
              (fun y hyBoundary hyRow =>
                (ValidShadeGrid.horizontal_none_weightsAt_zero valid
                  (if hy : y = row then by simpa [hy] using hat
                  else hbetween y hyBoundary (lt_of_le_of_ne hyRow hy))).1)
              hright)
          · have hmatch :=
              OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
                valid (column - 1) boundary
            have hcolumn : column - 1 + 1 = column := by omega
            rw [hcolumn, hleft] at hmatch
            have hfree :=
              OrientedLightFreeHeight.CycleShade.faceHeight_eq_one_of_freeRow
                shaded cycle valid (column := column - 1) (row := row)
                (by omega) (by omega) (by omega) hnorth free
            exact False.elim (positive_rightWeightAt_below_false
              shaded cycle valid (scan := column - 1) (row := row)
              (boundary := boundary) (by omega) (by omega)
              hboundarySouth hboundaryRow hnorth hfree
              (fun y hyBoundary hyRow => by
                have hnone : ShadedSignals.selectedHorizontalFor
                    (componentAt indexGrid column y) (quadrantAt column y)
                    (stateGrid column y) = none :=
                  if hy : y = row then by simpa [hy] using hat
                  else hbetween y hyBoundary (lt_of_le_of_ne hyRow hy)
                have hzero := ValidShadeGrid.horizontal_none_weightsAt_zero
                  valid hnone
                have hshared :=
                  OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
                    valid (column - 1) y
                rw [hcolumn, hzero.2] at hshared
                exact hshared) hmatch)

theorem exists_first_after
    {P : Nat -> Prop} {start finish : Nat}
    (hstart : start < finish) (hfinish : P finish) :
    exists first, start < first /\ first <= finish /\ P first /\
      forall value, start < value -> value < first -> Not (P value) := by
  classical
  let Q : Nat -> Prop := fun distance =>
    0 < distance /\ start + distance <= finish /\ P (start + distance)
  have existsQ : exists distance, Q distance := by
    refine ⟨finish - start, ?_⟩
    dsimp [Q]
    have hsum : start + (finish - start) = finish := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hfinish⟩
  let distance := Nat.find existsQ
  have found : Q distance := Nat.find_spec existsQ
  refine ⟨start + distance, by simpa [Q] using found.1,
    found.2.1, found.2.2, ?_⟩
  intro value hvalueStart hvalueFirst hvalue
  have candidate : Q (value - start) := by
    dsimp [Q]
    have hsum : start + (value - start) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsum] using hvalue⟩
  have minimal := Nat.find_min' existsQ candidate
  dsimp [distance] at hvalueFirst
  omega

theorem exists_last_before
    {P : Nat -> Prop} {first finish : Nat}
    (hfirst : first < finish) (hfirstP : P first) :
    exists last, first <= last /\ last < finish /\ P last /\
      forall value, last < value -> value < finish -> Not (P value) := by
  classical
  let Q : Nat -> Prop := fun distance =>
    0 < distance /\ distance <= finish - first /\ P (finish - distance)
  have existsQ : exists distance, Q distance := by
    refine ⟨finish - first, ?_⟩
    dsimp [Q]
    have hsub : finish - (finish - first) = first := by omega
    exact ⟨by omega, le_rfl, by simpa [hsub] using hfirstP⟩
  let distance := Nat.find existsQ
  have found : Q distance := Nat.find_spec existsQ
  refine ⟨finish - distance, by omega, by omega, found.2.2, ?_⟩
  intro value hlastValue hvalueFinish hvalue
  have candidate : Q (finish - value) := by
    dsimp [Q]
    have hsub : finish - (finish - value) = value := by omega
    exact ⟨by omega, by omega, by simpa [hsub] using hvalue⟩
  have minimal := Nat.find_min' existsQ candidate
  dsimp [distance] at hlastValue
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
  by_cases hat : selected row ≠ none
  · exact Or.inl hat
  have hatNone : selected row = none := not_ne_iff.mp hat
  have witness : exists boundary,
      quarterSouth south < boundary /\ boundary < quarterNorth north /\
        selected boundary ≠ none := by
    simp only [IsFreeColumn] at notFree
    push Not at notFree
    exact notFree
  rcases witness with ⟨boundary, hboundarySouth, hboundaryNorth, hselected⟩
  rcases lt_trichotomy row boundary with habove | hequal | hbelow
  · rcases exists_first_after (P := fun y => selected y ≠ none) habove hselected with
      ⟨first, hrowFirst, hfirstBoundary, hfirstSelected, hbetween⟩
    have hfirstNorth := hfirstBoundary.trans_lt hboundaryNorth
    have horiented := CycleShade.nearest_above_selected_north
      shaded cycle valid hwest heast hsouth hrowFirst hfirstNorth free
      hfirstSelected (fun y hyRow hyFirst =>
        not_ne_iff.mp (hbetween y hyRow hyFirst))
    exact Or.inr (Or.inl ⟨first, hrowFirst, hfirstNorth, horiented,
      fun y hyRow hyFirst => not_ne_iff.mp (hbetween y hyRow hyFirst)⟩)
  · subst boundary
    exact False.elim (hselected hatNone)
  · rcases exists_last_before (P := fun y => selected y ≠ none) hbelow hselected with
      ⟨last, hboundaryLast, hlastRow, hlastSelected, hbetween⟩
    have hlastSouth := hboundarySouth.trans_le hboundaryLast
    have horiented := CycleShade.nearest_below_selected_south
      shaded cycle valid hwest heast hlastSouth hlastRow hnorth free
      hatNone hlastSelected (fun y hyLast hyRow =>
        not_ne_iff.mp (hbetween y hyLast hyRow))
    exact Or.inr (Or.inr ⟨last, hlastSouth, hlastRow, horiented,
      fun y hyLast hyRow => not_ne_iff.mp (hbetween y hyLast hyRow)⟩)

end OrientedLightVerticalGeometry
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
