/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightHeight
import LeanWang.Robinson.Closed104.ShadedLightBoardFreeLines

/-!
# Unit height along free rows and columns

The face height is one on both sides of a free line.  Horizontally this follows
from the zero vertical weights on a free row; vertically it follows directly
from the recursive height definition and the zero horizontal weights on a
free column.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightFreeHeight

open OrientedRedCycles RedShadeCycles RedShadePaths ShadedPlaneSignalGrid
  OrientedLightSegments OrientedLightHeightWeights OrientedLightHeight
  Signals.FreeCellLocal

set_option maxRecDepth 20000

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

theorem ValidShadeGrid.horizontal_none_weightsAt_zero
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedHorizontalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) = none) :
    And (rightWeightAt stateGrid x y = 0)
      (leftWeightAt stateGrid x y = 0) := by
  simpa [rightWeightAt, leftWeightAt] using
    horizontal_none_weights_zero _ _ _ (valid.allowed x y) hselected

theorem ValidShadeGrid.vertical_none_weightsAt_zero
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    (hselected : ShadedSignals.selectedVerticalFor
      (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y) = none) :
    And (upWeightAt stateGrid x y = 0)
      (downWeightAt stateGrid x y = 0) := by
  simpa [upWeightAt, downWeightAt] using
    vertical_none_weights_zero _ _ _ (valid.allowed x y) hselected

/-- Absolute-coordinate form of the positive-height theorem. -/
theorem CycleShade.one_le_faceHeight_at
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west <= column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south <= row)
    (hnorth : row < quarterNorth north) :
    (1 : Int) <= faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) := by
  have hheight := OrientedLightHeight.CycleShade.one_le_faceHeight
    shaded cycle valid
    (xOffset := column - quarterWest west)
    (yOffset := row - quarterSouth south) (by omega) (by omega)
  have hx : quarterWest west + (column - quarterWest west) = column := by omega
  simpa only [hx] using hheight

/-- Every face on a free row has the outer board's height one. -/
theorem CycleShade.faceHeight_eq_one_of_freeRow
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west <= column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south <= row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeRow indexGrid stateGrid west east row) :
    faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  let rowOffset := row - quarterSouth south
  have hrow : quarterSouth south + rowOffset = row := by
    dsimp [rowOffset]
    omega
  have all : forall xOffset,
      quarterWest west + xOffset < quarterEast east ->
      faceHeight stateGrid (quarterWest west + xOffset)
        (quarterSouth south) rowOffset = 1 := by
    intro xOffset
    induction xOffset with
    | zero =>
        intro _
        have hheight := OrientedLightHeight.CycleShade.faceHeight_west
          shaded cycle valid (offset := rowOffset) (by omega)
        simpa using hheight
    | succ xOffset ih =>
        intro heastOffset
        have hprevious := ih (by omega)
        let column := quarterWest west + (xOffset + 1)
        have hnone := free column (by simp [column])
          (by simpa [column] using heastOffset)
        have hzero :=
          ValidShadeGrid.vertical_none_weightsAt_zero valid hnone
        have hdiff := OrientedLightHeight.CycleShade.faceHeight_sub_left
          shaded cycle valid (column := column) (offset := rowOffset)
          (by simp [column]) (by simpa [column] using heastOffset)
        have hleft : column - 1 = quarterWest west + xOffset := by
          simp [column]
        rw [hleft, hrow] at hdiff
        dsimp [column] at hdiff hzero
        omega
  have hheight := all (column - quarterWest west) (by omega)
  have hx : quarterWest west + (column - quarterWest west) = column := by omega
  simpa only [hx] using hheight

/-- Height immediately to the right of a free column is one. -/
theorem CycleShade.faceHeight_eq_one_right_of_freeColumn
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west <= column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south <= row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column) :
    faceHeight stateGrid column (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  let rowOffset := row - quarterSouth south
  have hrow : quarterSouth south + rowOffset = row := by
    dsimp [rowOffset]
    omega
  have all : forall offset,
      quarterSouth south + offset < quarterNorth north ->
      faceHeight stateGrid column (quarterSouth south) offset = 1 := by
    intro offset
    induction offset with
    | zero =>
        intro _
        exact OrientedLightHeight.CycleShade.faceHeight_south
          shaded cycle valid hwest heast
    | succ offset ih =>
        intro hnorthOffset
        have hprevious := ih (by omega)
        let y := quarterSouth south + offset + 1
        have hnone := free y (by simp [y])
          (by dsimp [y]; omega)
        have hzero :=
          ValidShadeGrid.horizontal_none_weightsAt_zero valid hnone
        rw [faceHeight, hprevious]
        have hy : quarterSouth south + offset + 1 = y := rfl
        rw [hy, hzero.1]
        omega
  exact all rowOffset (by omega)

/-- Height immediately to the left of a strict free column is one. -/
theorem CycleShade.faceHeight_eq_one_left_of_freeColumn
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column row : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east)
    (hsouth : quarterSouth south <= row)
    (hnorth : row < quarterNorth north)
    (free : IsFreeColumn indexGrid stateGrid south north column) :
    faceHeight stateGrid (column - 1) (quarterSouth south)
      (row - quarterSouth south) = 1 := by
  let rowOffset := row - quarterSouth south
  have all : forall offset,
      quarterSouth south + offset < quarterNorth north ->
      faceHeight stateGrid (column - 1) (quarterSouth south) offset = 1 := by
    intro offset
    induction offset with
    | zero =>
        intro _
        apply OrientedLightHeight.CycleShade.faceHeight_south
          shaded cycle valid
        · omega
        · omega
    | succ offset ih =>
        intro hnorthOffset
        have hprevious := ih (by omega)
        let y := quarterSouth south + offset + 1
        have hnone := free y (by simp [y])
          (by dsimp [y]; omega)
        have hzero :=
          ValidShadeGrid.horizontal_none_weightsAt_zero valid hnone
        have hmatch :=
          OrientedLightHeight.ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
            valid (column - 1) y
        have hcolumn : column - 1 + 1 = column := by omega
        rw [hcolumn, hzero.2] at hmatch
        rw [faceHeight, hprevious]
        have hy : quarterSouth south + offset + 1 = y := rfl
        rw [hy, hmatch]
        omega
  exact all rowOffset (by omega)

end OrientedLightFreeHeight
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
