/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.OrientedLightSegments

/-!
# Signed edge weights for directed light wires

Give every light edge weight `1` when its direction leaves the face on its
left and `-1` in the opposite direction.  At an allowed quarter tile the four
weights satisfy a discrete conservation law.  The same local audit also rules
out the pair of edges that would make a right turn at the southwest corner of
a face.

These are the only finite, construction-specific facts needed by the height
minimum argument.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightHeightWeights

open Figure16 RedCycles RedShadePaths OrientedLightSegments
  Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- Weight of a directed light edge.  `positive` specifies which of the two
directions gives weight `1`. -/
def edgeWeight (value : Option RedShades.Shade) (positive : Bool) : Int :=
  if value = some .light then
    if positive then 1 else -1
  else
    0

/-- Horizontal edge immediately to the right of a quarter tile. -/
def rightWeight (quadrant : Quadrant) (state : RedShades.State) : Int :=
  edgeWeight state.east quadrant.yBit

/-- Horizontal edge immediately to the left of a quarter tile. -/
def leftWeight (quadrant : Quadrant) (state : RedShades.State) : Int :=
  edgeWeight state.west quadrant.yBit

/-- Vertical edge immediately above a quarter tile, measured as the height
change from its left face to its right face. -/
def upWeight (quadrant : Quadrant) (state : RedShades.State) : Int :=
  edgeWeight state.north quadrant.xBit

/-- Vertical edge immediately below a quarter tile, measured as the height
change from its left face to its right face. -/
def downWeight (quadrant : Quadrant) (state : RedShades.State) : Int :=
  edgeWeight state.south quadrant.xBit


def segmentRightWeight : Segment -> Int
  | .east | .southEast => 1
  | .west | .westSouth => -1
  | .north | .south | .eastNorth | .northWest => 0

def segmentLeftWeight : Segment -> Int
  | .east | .eastNorth => 1
  | .west | .northWest => -1
  | .north | .south | .southEast | .westSouth => 0

def segmentUpWeight : Segment -> Int
  | .south | .southEast => 1
  | .north | .eastNorth => -1
  | .east | .west | .northWest | .westSouth => 0

def segmentDownWeight : Segment -> Int
  | .south | .westSouth => 1
  | .north | .northWest => -1
  | .east | .west | .southEast | .eastNorth => 0


theorem neg_one_le_edgeWeight (value : Option RedShades.Shade)
    (positive : Bool) : (-1 : Int) <= edgeWeight value positive := by
  unfold edgeWeight
  split_ifs <;> omega

theorem edgeWeight_le_one (value : Option RedShades.Shade)
    (positive : Bool) : edgeWeight value positive <= (1 : Int) := by
  unfold edgeWeight
  split_ifs <;> omega

theorem neg_one_le_rightWeight (quadrant : Quadrant)
    (state : RedShades.State) : (-1 : Int) <= rightWeight quadrant state :=
  neg_one_le_edgeWeight _ _

theorem rightWeight_le_one (quadrant : Quadrant)
    (state : RedShades.State) : rightWeight quadrant state <= (1 : Int) :=
  edgeWeight_le_one _ _

theorem neg_one_le_upWeight (quadrant : Quadrant)
    (state : RedShades.State) : (-1 : Int) <= upWeight quadrant state :=
  neg_one_le_edgeWeight _ _

theorem upWeight_le_one (quadrant : Quadrant)
    (state : RedShades.State) : upWeight quadrant state <= (1 : Int) :=
  edgeWeight_le_one _ _

private theorem thick_mem_all (component : Thick) : component ∈ Thick.all := by
  cases component <;> decide

private def segmentAll : List Segment :=
  [.east, .north, .west, .south,
    .southEast, .eastNorth, .northWest, .westSouth]

private theorem segment_mem_all (segment : Segment) : segment ∈ segmentAll := by
  cases segment <;> decide

local instance : Fintype Thick := Fintype.ofList Thick.all thick_mem_all
local instance : Fintype Quadrant := Fintype.ofList Quadrant.all Quadrant.mem_all
local instance : Fintype RedShades.State :=
  Fintype.ofList RedShades.State.all RedShades.State.mem_all
local instance : Fintype Segment := Fintype.ofList segmentAll segment_mem_all

set_option linter.style.nativeDecide false in
/-- The signed light flow has zero divergence at every allowed quarter tile. -/
theorem balance_of_allowed (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true) :
    rightWeight quadrant state - leftWeight quadrant state =
      upWeight quadrant state - downWeight quadrant state := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
/-- The four geometric weights agree with the segment read from an allowed
quarter tile. -/
theorem weights_eq_of_segment (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) (segment : Segment)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hsegment : segment? component quadrant state = some segment) :
    rightWeight quadrant state = segmentRightWeight segment /\
      leftWeight quadrant state = segmentLeftWeight segment /\
      upWeight quadrant state = segmentUpWeight segment /\
      downWeight quadrant state = segmentDownWeight segment := by
  revert component quadrant state segment
  native_decide

set_option linter.style.nativeDecide false in
/-- A west-pointing bottom edge and a north-pointing left edge would be a
right turn, so they cannot meet at an allowed quarter tile. -/
theorem not_right_negative_and_up_negative_of_allowed
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true) :
    Not (rightWeight quadrant state = -1 /\ upWeight quadrant state = -1) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_none_weights_zero
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state = none) :
    And (rightWeight quadrant state = 0) (leftWeight quadrant state = 0) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem vertical_none_weights_zero
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state = none) :
    And (upWeight quadrant state = 0) (downWeight quadrant state = 0) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_south_has_negative_weight
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state = some .south) :
    Or (rightWeight quadrant state = -1) (leftWeight quadrant state = -1) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem horizontal_north_has_positive_weight
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedHorizontalFor component quadrant state = some .north) :
    Or (rightWeight quadrant state = 1) (leftWeight quadrant state = 1) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem vertical_west_has_negative_weight
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state = some .west) :
    Or (upWeight quadrant state = -1) (downWeight quadrant state = -1) := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem vertical_east_has_positive_weight
    (component : Thick) (quadrant : Quadrant) (state : RedShades.State)
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hselected : ShadedSignals.selectedVerticalFor component quadrant state = some .east) :
    Or (upWeight quadrant state = 1) (downWeight quadrant state = 1) := by
  revert component quadrant state
  native_decide

theorem ValidShadeGrid.rightWeight_eq_leftWeight_succ
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    rightWeight (quadrantAt x y) (stateGrid x y) =
      leftWeight (quadrantAt (x + 1) y) (stateGrid (x + 1) y) := by
  unfold rightWeight leftWeight
  rw [valid.hmatch x y]
  simp only [OrientedLightSegments.quadrantAt_yBit]

theorem ValidShadeGrid.upWeight_eq_downWeight_succ
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    upWeight (quadrantAt x y) (stateGrid x y) =
      downWeight (quadrantAt x (y + 1)) (stateGrid x (y + 1)) := by
  unfold upWeight downWeight
  rw [valid.vmatch x y]
  simp only [OrientedLightSegments.quadrantAt_xBit]

theorem ValidShadeGrid.weightsAt_of_segment
    {indexGrid : Nat -> Nat -> Index}
    {stateGrid : Nat -> Nat -> RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) {x y : Nat}
    {segment : Segment}
    (hsegment : segmentAt indexGrid stateGrid x y = some segment) :
    rightWeight (quadrantAt x y) (stateGrid x y) = segmentRightWeight segment /\
      leftWeight (quadrantAt x y) (stateGrid x y) = segmentLeftWeight segment /\
      upWeight (quadrantAt x y) (stateGrid x y) = segmentUpWeight segment /\
      downWeight (quadrantAt x y) (stateGrid x y) = segmentDownWeight segment :=
  weights_eq_of_segment _ _ _ _ (valid.allowed x y) hsegment

end OrientedLightHeightWeights
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
