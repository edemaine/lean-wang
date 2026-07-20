/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShades
import LeanWang.Robinson.Closed104.SignalFreeCellLocal
import LeanWang.Robinson.Closed104.SignalCorridors

/-!
# Propagating red-wire shades

`ValidShadeGrid` is the semantic form of the red shade layer: each quarter
state is locally allowed for its thick Robinson component, and neighboring
states agree on shared edges.  A present straight line therefore transmits one
shade unchanged, a corner identifies its two incident shades, and a crossing
forces the horizontal and vertical shades to be opposite.

This file exposes those local consequences and lifts straight-line
transmission to arbitrary finite intervals.  Later graph modules package the
same equal/opposite relation as a parity-labelled path, while `RedShadeCycles`
uses the interval form around rectangular board boundaries.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadePaths

open RedCycles Signals.FreeCellLocal

set_option maxRecDepth 20000

/-- A locally allowed, edge-matching shade assignment over a quarter grid. -/
structure ValidShadeGrid (indexGrid : Nat → Nat → Index)
    (stateGrid : Nat → Nat → RedShades.State) : Prop where
  allowed : ∀ x y,
    RedShades.locallyAllowed
      (indexGrid (x / 2) (y / 2), quadrantAt x y) (stateGrid x y) = true
  hmatch : ∀ x y, (stateGrid x y).east = (stateGrid (x + 1) y).west
  vmatch : ∀ x y, (stateGrid x y).north = (stateGrid x (y + 1)).south

private theorem ValidShadeGrid.allowedFor
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat) :
    RedShades.allowedFor (componentAt indexGrid x y) (quadrantAt x y)
      (stateGrid x y) = true := by
  simpa [RedShades.locallyAllowed, componentAt] using valid.allowed x y

theorem ValidShadeGrid.horizontal_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasHorizontal
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).east :=
  RedShades.horizontal_eq_of_allowedFor (valid.allowedFor x y) hpath

theorem ValidShadeGrid.vertical_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasVertical
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).south = (stateGrid x y).north :=
  RedShades.vertical_eq_of_allowedFor (valid.allowedFor x y) hpath

theorem ValidShadeGrid.east_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasEast
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).east.isSome = true :=
  RedShades.east_present_of_allowedFor (valid.allowedFor x y) hpath

theorem ValidShadeGrid.west_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasWest
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west.isSome = true :=
  RedShades.west_present_of_allowedFor (valid.allowedFor x y) hpath

theorem ValidShadeGrid.south_present
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hpath : RedShades.hasSouth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).south.isSome = true :=
  RedShades.south_present_of_allowedFor (valid.allowedFor x y) hpath

theorem ValidShadeGrid.west_north_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : RedShades.cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hnorth : RedShades.cornerNorth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).north :=
  RedShades.west_north_corner_eq_of_allowedFor
    (valid.allowedFor x y) hwest hnorth

theorem ValidShadeGrid.west_south_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hwest : RedShades.cornerWest
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hsouth : RedShades.cornerSouth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west = (stateGrid x y).south :=
  RedShades.west_south_corner_eq_of_allowedFor
    (valid.allowedFor x y) hwest hsouth

theorem ValidShadeGrid.east_north_corner_eq
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (heast : RedShades.cornerEast
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hnorth : RedShades.cornerNorth
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).east = (stateGrid x y).north :=
  RedShades.east_north_corner_eq_of_allowedFor
    (valid.allowedFor x y) heast hnorth

theorem ValidShadeGrid.crossing_opposite
    {indexGrid : Nat → Nat → Index} {stateGrid : Nat → Nat → RedShades.State}
    (valid : ValidShadeGrid indexGrid stateGrid) (x y : Nat)
    (hhorizontal : RedShades.hasHorizontal
      (componentAt indexGrid x y) (quadrantAt x y) = true)
    (hvertical : RedShades.hasVertical
      (componentAt indexGrid x y) (quadrantAt x y) = true) :
    (stateGrid x y).west ≠ (stateGrid x y).south :=
  RedShades.crossing_opposite_of_allowedFor
    (valid.allowedFor x y) hhorizontal hvertical

/-- Equality of horizontal shade across a sequence of path quarters. -/
theorem horizontal_shade_across
    (state : Nat → RedShades.State) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      (state (start + i)).east = (state (start + i + 1)).west)
    (htransmit : ∀ i, i < count →
      (state (start + i + 1)).west = (state (start + i + 1)).east) :
    (state start).east = (state (start + count + 1)).west :=
  Signals.value_across state RedShades.State.east RedShades.State.west
    start count hmatch htransmit

/-- Equality of vertical shade across a sequence of path quarters. -/
theorem vertical_shade_across
    (state : Nat → RedShades.State) (start count : Nat)
    (hmatch : ∀ i, i ≤ count →
      (state (start + i)).north = (state (start + i + 1)).south)
    (htransmit : ∀ i, i < count →
      (state (start + i + 1)).south = (state (start + i + 1)).north) :
    (state start).north = (state (start + count + 1)).south :=
  Signals.value_across state RedShades.State.north RedShades.State.south
    start count hmatch htransmit

end RedShadePaths
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
