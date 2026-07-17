/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightBoards
import LeanWang.Robinson.Closed104.OrientedLightHeightWeights

/-!
# A height minimum principle for light wires

The height of a face is the signed number of horizontal light edges crossed
from the bottom of a light Robinson board.  Edge matching and local
conservation make this a genuine two-dimensional height function.

Every face strictly inside the board has height at least one.  The proof is a
discrete minimum principle: if an interior face had smaller height than both
its left and lower neighbors, its southwest vertex would contain a west edge
entering from the right and a north edge leaving upward.  That is precisely a
forbidden right turn.  Strong induction moves any hypothetical low face to
the south or west boundary, where the counterclockwise outer wire gives
height one.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightHeight

open OrientedRedCycles RedShadeCycles RedShadePaths
  OrientedLightSegments OrientedLightBoards OrientedLightHeightWeights
  Signals.FreeCellLocal

set_option maxRecDepth 20000

def rightWeightAt (stateGrid : Nat -> Nat -> RedShades.State)
    (x y : Nat) : Int :=
  rightWeight (quadrantAt x y) (stateGrid x y)

def leftWeightAt (stateGrid : Nat -> Nat -> RedShades.State)
    (x y : Nat) : Int :=
  leftWeight (quadrantAt x y) (stateGrid x y)

def upWeightAt (stateGrid : Nat -> Nat -> RedShades.State)
    (x y : Nat) : Int :=
  upWeight (quadrantAt x y) (stateGrid x y)

def downWeightAt (stateGrid : Nat -> Nat -> RedShades.State)
    (x y : Nat) : Int :=
  downWeight (quadrantAt x y) (stateGrid x y)

/-- Height of the face above the horizontal edge at `bottom + offset`, on the
vertical scan immediately to the right of `column`. -/
def faceHeight (stateGrid : Nat -> Nat -> RedShades.State)
    (column bottom : Nat) : Nat -> Int
  | 0 => rightWeightAt stateGrid column bottom
  | offset + 1 =>
      faceHeight stateGrid column bottom offset +
        rightWeightAt stateGrid column (bottom + offset + 1)

theorem ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    rightWeightAt stateGrid x y = leftWeightAt stateGrid (x + 1) y :=
  OrientedLightHeightWeights.ValidShadeGrid.rightWeight_eq_leftWeight_succ valid x y

theorem ValidShadeGrid.upWeightAt_eq_downWeightAt_succ
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    upWeightAt stateGrid x y = downWeightAt stateGrid x (y + 1) :=
  OrientedLightHeightWeights.ValidShadeGrid.upWeight_eq_downWeight_succ valid x y

theorem ValidShadeGrid.balanceAt
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    rightWeightAt stateGrid x y - leftWeightAt stateGrid x y =
      upWeightAt stateGrid x y - downWeightAt stateGrid x y :=
  balance_of_allowed _ _ _ (valid.allowed x y)

variable {indexGrid : Nat -> Nat -> Index}
  {stateGrid : Nat -> Nat -> RedShades.State}
  {west east south north : Nat}

private theorem CycleShade.south_rightWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x : Nat} (hwest : quarterWest west <= x)
    (heast : x < quarterEast east) :
    rightWeightAt stateGrid x (quarterSouth south) = 1 := by
  rcases hwest.eq_or_lt with rfl | hwest
  · have hsegment := OrientedLightBoards.CycleShade.southwest_segment shaded cycle valid
    have hweights := OrientedLightHeightWeights.ValidShadeGrid.weightsAt_of_segment valid hsegment
    simpa [rightWeightAt, segmentRightWeight] using hweights.1
  · have hsegment := OrientedLightBoards.CycleShade.south_segment shaded cycle valid hwest heast
    have hweights := OrientedLightHeightWeights.ValidShadeGrid.weightsAt_of_segment valid hsegment
    simpa [rightWeightAt, segmentRightWeight] using hweights.1

private theorem CycleShade.south_upWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {x : Nat} (hwest : quarterWest west < x)
    (heast : x < quarterEast east) :
    upWeightAt stateGrid x (quarterSouth south) = 0 := by
  have hsegment := OrientedLightBoards.CycleShade.south_segment shaded cycle valid hwest heast
  have hweights := OrientedLightHeightWeights.ValidShadeGrid.weightsAt_of_segment valid hsegment
  simpa [upWeightAt, segmentUpWeight] using hweights.2.2.1

private theorem CycleShade.west_rightWeightAt
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {y : Nat} (hsouth : quarterSouth south < y)
    (hnorth : y < quarterNorth north) :
    rightWeightAt stateGrid (quarterWest west) y = 0 := by
  have hsegment := OrientedLightBoards.CycleShade.west_segment shaded cycle valid hsouth hnorth
  have hweights := OrientedLightHeightWeights.ValidShadeGrid.weightsAt_of_segment valid hsegment
  simpa [rightWeightAt, segmentRightWeight] using hweights.1

theorem CycleShade.faceHeight_south
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column : Nat} (hwest : quarterWest west <= column)
    (heast : column < quarterEast east) :
    faceHeight stateGrid column (quarterSouth south) 0 = 1 := by
  simpa [faceHeight] using CycleShade.south_rightWeightAt shaded cycle valid hwest heast

theorem CycleShade.faceHeight_west
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {offset : Nat}
    (hnorth : quarterSouth south + offset < quarterNorth north) :
    faceHeight stateGrid (quarterWest west) (quarterSouth south) offset = 1 := by
  revert hnorth
  induction offset with
  | zero =>
      intro _
      apply CycleShade.faceHeight_south shaded cycle valid
      · exact le_rfl
      · have := cycle.west_lt_east
        simp [quarterWest, quarterEast] at this ⊢
        omega
  | succ offset ih =>
      intro hnorth
      have hprevious : quarterSouth south + offset < quarterNorth north := by
        omega
      have hside := CycleShade.west_rightWeightAt shaded cycle valid
        (y := quarterSouth south + offset + 1) (by omega) hnorth
      rw [faceHeight, ih hprevious, hside]
      omega

/-- Horizontal variation of face height is the signed vertical edge at the
shared vertex. -/
theorem CycleShade.faceHeight_sub_left
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {column offset : Nat}
    (hwest : quarterWest west < column)
    (heast : column < quarterEast east) :
    faceHeight stateGrid column (quarterSouth south) offset -
        faceHeight stateGrid (column - 1) (quarterSouth south) offset =
      upWeightAt stateGrid column (quarterSouth south + offset) := by
  induction offset with
  | zero =>
      have hleft : quarterWest west <= column - 1 := by omega
      have hleftEast : column - 1 < quarterEast east := by omega
      have hrightWeight := CycleShade.south_rightWeightAt shaded cycle valid
        (x := column) (le_of_lt hwest) heast
      have hleftWeight := CycleShade.south_rightWeightAt shaded cycle valid
        (x := column - 1) hleft hleftEast
      have hup := CycleShade.south_upWeightAt shaded cycle valid hwest heast
      simpa [faceHeight] using show
        rightWeightAt stateGrid column (quarterSouth south) -
            rightWeightAt stateGrid (column - 1) (quarterSouth south) =
          upWeightAt stateGrid column (quarterSouth south) by omega
  | succ offset ih =>
      have hcolumn : column - 1 + 1 = column := by omega
      have hhorizontal := ValidShadeGrid.rightWeightAt_eq_leftWeightAt_succ valid
        (column - 1) (quarterSouth south + offset + 1)
      rw [hcolumn] at hhorizontal
      have hlocal := ValidShadeGrid.balanceAt valid column
        (quarterSouth south + offset + 1)
      have hvertical := ValidShadeGrid.upWeightAt_eq_downWeightAt_succ valid
        column (quarterSouth south + offset)
      have hy : quarterSouth south + offset + 1 =
          quarterSouth south + (offset + 1) := by omega
      rw [hy] at hhorizontal hlocal hvertical
      simp only [faceHeight]
      rw [hy]
      omega

/-- The counterclockwise outer board and the absence of right turns give a
discrete minimum principle: every strict interior face has positive height. -/
theorem CycleShade.one_le_faceHeight
    (shaded : CycleShade stateGrid west east south north .light)
    (cycle : CycleOn indexGrid west east south north)
    (valid : ValidShadeGrid indexGrid stateGrid)
    {xOffset yOffset : Nat}
    (heast : quarterWest west + xOffset < quarterEast east)
    (hnorth : quarterSouth south + yOffset < quarterNorth north) :
    (1 : Int) <= faceHeight stateGrid
      (quarterWest west + xOffset) (quarterSouth south) yOffset := by
  have all : forall n xOffset yOffset : Nat,
      xOffset + yOffset = n ->
      quarterWest west + xOffset < quarterEast east ->
      quarterSouth south + yOffset < quarterNorth north ->
      (1 : Int) <= faceHeight stateGrid
        (quarterWest west + xOffset) (quarterSouth south) yOffset := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xOffset yOffset hsum heast hnorth
        cases xOffset with
        | zero =>
            have hwestHeight := CycleShade.faceHeight_west shaded cycle valid hnorth
            simp [hwestHeight]
        | succ xOffset =>
            cases yOffset with
            | zero =>
                have hsouthHeight := CycleShade.faceHeight_south shaded cycle valid
                  (column := quarterWest west + (xOffset + 1)) (by omega) (by omega)
                omega
            | succ yOffset =>
                have hleft := ih (xOffset + (yOffset + 1)) (by omega)
                  xOffset (yOffset + 1) rfl (by omega) (by omega)
                have hbelow := ih ((xOffset + 1) + yOffset) (by omega)
                  (xOffset + 1) yOffset rfl (by omega) (by omega)
                by_contra hlow
                have hcurrent : faceHeight stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south) (yOffset + 1) < 1 := by
                  omega
                have hdiff := CycleShade.faceHeight_sub_left shaded cycle valid
                  (column := quarterWest west + (xOffset + 1))
                  (offset := yOffset + 1) (by omega) (by omega)
                have hleftColumn :
                    quarterWest west + (xOffset + 1) - 1 =
                      quarterWest west + xOffset := by omega
                rw [hleftColumn] at hdiff
                have hupLower := neg_one_le_upWeight
                  (quadrantAt
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)))
                  (stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)))
                have hupLowerAt : (-1 : Int) <= upWeightAt stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)) := by
                  simpa [upWeightAt] using hupLower
                have hup : upWeightAt stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)) = -1 := by
                  omega
                have hrightLower := neg_one_le_rightWeight
                  (quadrantAt
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)))
                  (stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)))
                have hrightLowerAt : (-1 : Int) <= rightWeightAt stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)) := by
                  simpa [rightWeightAt] using hrightLower
                have hright : rightWeightAt stateGrid
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)) = -1 := by
                  simp only [faceHeight] at hcurrent
                  rw [show quarterSouth south + yOffset + 1 =
                    quarterSouth south + (yOffset + 1) by omega] at hcurrent
                  omega
                exact not_right_negative_and_up_negative_of_allowed
                  _ _ _ (valid.allowed
                    (quarterWest west + (xOffset + 1))
                    (quarterSouth south + (yOffset + 1)))
                  ⟨by simpa [rightWeightAt] using hright,
                    by simpa [upWeightAt] using hup⟩
  exact all (xOffset + yOffset) xOffset yOffset rfl heast hnorth

end OrientedLightHeight
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
