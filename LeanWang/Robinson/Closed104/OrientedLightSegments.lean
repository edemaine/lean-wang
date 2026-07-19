/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.ShadedSignals
import LeanWang.Robinson.Closed104.RedShadePaths

/-!
# Directed light-red segments

The light part of an allowed shaded quarter tile is either absent, a straight
segment, or one of four left turns. This small physical model forgets the
parity-changing crossing links used by the refinement search graph: at a red
crossing, exactly one of the two wires is light.

The finite local audits below are the only construction-specific input.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace OrientedLightSegments

open Figure16 RedCycles RedShadePaths Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- The eight possible nonempty light-wire shapes in an allowed quarter. -/
inductive Segment where
  | east
  | north
  | west
  | south
  | southEast
  | eastNorth
  | northWest
  | westSouth
deriving DecidableEq, Repr

/-- Read the directed light segment from the two selected border values. -/
def segment? (component : Thick) (quadrant : Quadrant)
    (state : RedShades.State) : Option Segment :=
  match ShadedSignals.selectedVerticalFor component quadrant state,
      ShadedSignals.selectedHorizontalFor component quadrant state with
  | none, none => none
  | none, some .north => some .east
  | some .west, none => some .north
  | none, some .south => some .west
  | some .east, none => some .south
  | some .east, some .north => some .southEast
  | some .west, some .north => some .eastNorth
  | some .west, some .south => some .northWest
  | some .east, some .south => some .westSouth

private theorem thick_mem_all (component : Thick) : component ∈ Thick.all := by
  cases component <;> decide

local instance : Fintype Thick := Fintype.ofList Thick.all thick_mem_all
local instance : Fintype RedShades.State :=
  Fintype.ofList RedShades.State.all RedShades.State.mem_all

set_option linter.style.nativeDecide false in
theorem segment_eq_east_of_horizontal_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hwest : state.west = some .light) (heast : state.east = some .light)
    (hbit : quadrant.yBit = true) :
    segment? component quadrant state = some .east := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_west_of_horizontal_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hwest : state.west = some .light) (heast : state.east = some .light)
    (hbit : quadrant.yBit = false) :
    segment? component quadrant state = some .west := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_north_of_vertical_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hsouth : state.south = some .light) (hnorth : state.north = some .light)
    (hbit : quadrant.xBit = false) :
    segment? component quadrant state = some .north := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_south_of_vertical_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hsouth : state.south = some .light) (hnorth : state.north = some .light)
    (hbit : quadrant.xBit = true) :
    segment? component quadrant state = some .south := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_southEast_of_turn_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (heast : state.east = some .light) (hnorth : state.north = some .light)
    (hx : quadrant.xBit = true) (hy : quadrant.yBit = true) :
    segment? component quadrant state = some .southEast := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_eastNorth_of_turn_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hwest : state.west = some .light) (hnorth : state.north = some .light)
    (hx : quadrant.xBit = false) (hy : quadrant.yBit = true) :
    segment? component quadrant state = some .eastNorth := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_northWest_of_turn_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (hwest : state.west = some .light) (hsouth : state.south = some .light)
    (hx : quadrant.xBit = false) (hy : quadrant.yBit = false) :
    segment? component quadrant state = some .northWest := by
  revert component quadrant state
  native_decide

set_option linter.style.nativeDecide false in
theorem segment_eq_westSouth_of_turn_edges
    {component : Thick} {quadrant : Quadrant} {state : RedShades.State}
    (allowed : RedShades.allowedFor component quadrant state = true)
    (heast : state.east = some .light) (hsouth : state.south = some .light)
    (hx : quadrant.xBit = true) (hy : quadrant.yBit = false) :
    segment? component quadrant state = some .westSouth := by
  revert component quadrant state
  native_decide

@[simp] theorem quadrantAt_xBit (x y : Nat) :
    (quadrantAt x y).xBit = (x % 2 == 1) := by
  cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
    simp [quadrantAt, hx, hy, Quadrant.ofBits, Quadrant.xBit]

@[simp] theorem quadrantAt_yBit (x y : Nat) :
    (quadrantAt x y).yBit = (y % 2 == 1) := by
  cases hx : (x % 2 == 1) <;> cases hy : (y % 2 == 1) <;>
    simp [quadrantAt, hx, hy, Quadrant.ofBits, Quadrant.yBit]

/-- Directed segment at an absolute quarter-grid coordinate. -/
def segmentAt (indexGrid : Nat -> Nat -> Index)
    (stateGrid : Nat -> Nat -> RedShades.State) (x y : Nat) : Option Segment :=
  segment? (componentAt indexGrid x y) (quadrantAt x y) (stateGrid x y)

end OrientedLightSegments
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
